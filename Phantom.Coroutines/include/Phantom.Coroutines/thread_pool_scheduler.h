#pragma once

#include "detail/coroutine.h"
#include "read_copy_update.h"
#include "scheduler.h"
#include "task.h"
#include <algorithm>
#include <atomic>
#include <shared_mutex>
#include <unordered_set>
#include <unordered_map>
#include <vector>

namespace Phantom::Coroutines
{
namespace detail
{

// The thread_pool_scheduler implements the algorithms in ThreadPool.tla
// and ThreadPool_Wakeup.tla.
class thread_pool_scheduler
{
	class thread_state
	{
		class queue
		{
			std::vector<std::coroutine_handle<>> m_continuations;
			size_t m_startIndex;
		public:
			queue(
				size_t size = 1024
			) : m_startIndex{ 0 }
			{
				m_continuations.resize(size);
			}

			size_t size()
			{
				return m_continuations.size();
			}

			coroutine_handle<>& operator[](size_t index)
			{
				return m_continuations[(index - m_startIndex) % m_continuations.size()];
			}
			
			queue grow(
				size_t requiredSize,
				size_t tail,
				size_t head
			)
			{
				queue result(requiredSize * 2);
				result.m_startIndex = tail;
				for (auto index = tail; index < head; index++)
				{
					result[index] = (*this)[index];
				}
				return result;
			}
		};

		// Start with variables that are read-only or have very little contention.
		std::atomic<size_t> m_head;
		// The maximum value that m_head may contain without recalcuating 
		// both this value and possibly regrowing the queue.
		size_t m_reservedHead = 0;
		thread_pool_scheduler& m_scheduler;

		// This stores the state of whether the thread is intending
		// to sleep. While sleeping, the thread waits on this variable.
		std::atomic<bool> m_isSleeping;

		read_copy_update_section<queue> m_queueReadCopyUpdateSection;

		// Align the tail, copy count, and lock into a new cache line.
		alignas(std::hardware_destructive_interference_size)
			std::atomic<size_t> m_tail;
		// The number of items being copied from the queue.
		// This is incremented before m_tail is increased,
		// and decremented after the copy operation completes.
		// It is used to allow determining whether enqueue
		// needs to allocate more space.
		// Note that it starts at 1, because we always consider
		// that there is an extra operation stored in temporary
		// space after "head" is decremented when processing a local item.
		std::atomic<size_t> m_outstandingCopyOperationCount = 1;

		// The lock required for stealing and conflict resolution between
		// stealing and enqueuing.
		std::mutex m_mutex;

		void reserve_queue_space(
			size_t newHead,
			read_copy_update_section<queue>::update_operation& queueOperation
		)
		{
			if (m_reservedHead < newHead)
			{
				recalculate_reserved_size_and_grow_queue_if_necessary(
					newHead,
					queueOperation
				);
			}
		}

		void recalculate_reserved_size_and_grow_queue_if_necessary(
			size_t newHead,
			read_copy_update_section<queue>::update_operation& queueOperation
		)
		{
			auto tail = m_tail.load(std::memory_order_acquire);
			// m_outstandingCopyOperationCount can be loaded as relaxed, because its increments are preceded by
			// increments to tail and then m_outstandingCopyOperationCount decreases in value.
			// The acquire on tail ensures that we receive the value.
			auto outstandingCopyOperationCount = m_outstandingCopyOperationCount.load(std::memory_order_relaxed);

			auto requiredSize = newHead - tail + outstandingCopyOperationCount;

			if (queueOperation.value().size() < requiredSize)
			{
				queueOperation.emplace(
					queueOperation.value().grow(
						requiredSize,
						tail - outstandingCopyOperationCount,
						m_head.load(std::memory_order_relaxed)
					)
				);
				queueOperation.exchange();
			}

			// Reserve 1 for the temporary item that processing an item locally requires.
			m_reservedHead = tail - outstandingCopyOperationCount + queueOperation->size();
		}

	public:
		thread_state(
			thread_pool_scheduler& scheduler
		) : m_scheduler{ scheduler }
		{}

		void enqueue(
			std::coroutine_handle<> continuation
		)
		{
			auto queueOperation = m_queueReadCopyUpdateSection.update();
			auto head = m_head.load(std::memory_order_relaxed);
			auto newHead = head + 1;

			reserve_queue_space(
				newHead,
				queueOperation);

			queueOperation.value()[head] = continuation;
			m_head.store(newHead, std::memory_order_release);
		}

		[[nodiscard]] bool try_wake()
		{
			bool isSleeping = m_isSleeping.load(std::memory_order_acquire);
			
			bool doWakeThread = isSleeping && m_isSleeping.exchange(
				false,
				std::memory_order_release
			);
			
			if (doWakeThread)
			{
				m_isSleeping.notify_all();
			}

			return doWakeThread;
		}

		coroutine_handle<> acquire_local_item()
		{
			auto head = m_head.load(std::memory_order_relaxed);
			// Special case, since head is unsigned
			if (head == 0) { return coroutine_handle<>{}; }
			head--;
			m_head.store(head, std::memory_order_relaxed);

			auto tail = m_tail.load(std::memory_order_acquire);
			if (tail > head)
			{
				std::scoped_lock lock{ m_mutex };
				tail = m_tail.load(std::memory_order_acquire);
				if (tail > head)
				{
					head++;
					m_head.store(head, std::memory_order_relaxed);
					return coroutine_handle<>{};
				}
			}

			auto coroutine = (*m_queueReadCopyUpdateSection)[head];
			
			return coroutine;
		}

		enum class steal_mode
		{
			Approximate,
			Precise
		};

		coroutine_handle<> try_steal(
			thread_state& other,
			steal_mode stealMode
		)
		{
			std::unique_lock lock{ other.m_mutex, std::defer_lock };
			if (stealMode == steal_mode::Precise)
			{
				lock.lock();
			}

			auto otherHead = other.m_head.load(std::memory_order_relaxed);
			auto otherTail = other.m_tail.load(std::memory_order_relaxed);
			if (otherHead <= otherTail)
			{
				return coroutine_handle<>{};
			}

			if (stealMode == steal_mode::Approximate)
			{
				if (!lock.try_lock())
				{
					return coroutine_handle<>{};
				}

				otherHead = other.m_head.load(std::memory_order_relaxed);
				otherTail = other.m_tail.load(std::memory_order_relaxed);
				if (otherHead <= otherTail)
				{
					return coroutine_handle<>{};
				}
			}

			// We are here, that means we can legitemately steal.
			// We steal half (rounded up) of the items in the source thread.
			size_t sizeToSteal = (otherHead - otherTail + 1) / 2;
			other.m_outstandingCopyOperationCount.fetch_add(
				sizeToSteal,
				std::memory_order_relaxed
			);
			other.m_tail.store(otherTail + sizeToSteal, std::memory_order_release);

			// It's possible that acquire_local_item has raced with this method,
			// and the other's head is now lower than the tail we published.
			// The other instance will acquire the lock before doing any more
			// processing, and we will adjust the m_outstandingCopyOperationCount
			// and m_tail accordingly.
			auto newOtherHead = other.m_head.load(std::memory_order_acquire);
			if (newOtherHead <= otherTail)
			{
				// We have to give back all the items, and do not process anything.
				other.m_tail.store(otherTail, std::memory_order_release);
				other.m_outstandingCopyOperationCount.fetch_sub(
					sizeToSteal,
					std::memory_order_relaxed
				);
				return std::coroutine_handle<>{};
			} else if (newOtherHead < otherTail + sizeToSteal)
			{
				// We have to give back some of the items.
				// We'll again target taking 1/2 of the items in the queue, rounded up.
				auto newSizeToSteal = (newOtherHead - otherTail + 1) / 2;
				auto countToGiveBack = sizeToSteal - newSizeToSteal;
				other.m_tail.store(otherTail + newSizeToSteal, std::memory_order_release);
				other.m_outstandingCopyOperationCount.fetch_sub(countToGiveBack, std::memory_order_relaxed);
				sizeToSteal = newSizeToSteal;
			}

			// We no longer need the lock.
			// We've reserved enough space in the queue via m_outstandingCopyOperationCount that
			// we can start a read only queue operation in the source to copy the items
			// into our queue.
			lock.unlock();

			auto otherQueueOperation = other.m_queueReadCopyUpdateSection.read();
			auto thisQueueOperation = m_queueReadCopyUpdateSection.update();

			// We copy all but one of the items from the source queue.
			// The last item we return as the item to process.
			auto head = m_head.load(std::memory_order_relaxed);
			auto newHead = head + sizeToSteal - 1;

			reserve_queue_space(
				newHead,
				thisQueueOperation
			);

			for (auto itemCounter = 0; itemCounter < (sizeToSteal - 1); itemCounter++)
			{
				(*thisQueueOperation)[head + itemCounter] = (*otherQueueOperation)[otherTail + itemCounter];
			}
			m_head.store(newHead, std::memory_order_release);
			auto itemToProcess = (*otherQueueOperation)[otherTail + sizeToSteal - 1];
			
			other.m_outstandingCopyOperationCount.fetch_sub(sizeToSteal, std::memory_order_relaxed);
			
			return itemToProcess;
		}

		coroutine_handle<> acquire_remote_item()
		{
			auto threadStatesReadOperation = m_scheduler.m_threadStatesSection.read();

			// First try to acquire something without blocking.
			for (auto& threadState : threadStatesReadOperation->m_threadStates)
			{
				auto remoteItem = try_steal(
					*threadState.second,
					steal_mode::Approximate
				);
				if (remoteItem)
				{
					return remoteItem;
				}
			}

			// Now try to acquire something with blocking.
			for (auto& threadState : threadStatesReadOperation->m_threadStates)
			{
				auto remoteItem = try_steal(
					*threadState.second,
					steal_mode::Approximate
				);
				if (remoteItem)
				{
					return remoteItem;
				}
			}

			return coroutine_handle<>{};
		}

		void mark_intent_to_sleep()
		{
			bool wasSleeping = m_isSleeping.exchange(true, std::memory_order_acquire);
			if (!wasSleeping)
			{
				m_scheduler.m_sleepingThreadCount.fetch_add(1, std::memory_order_release);
			}
		}
		
		void sleep(
			std::stop_token& stopToken
		)
		{
			if (stopToken.stop_requested())
			{
				return;
			}
			m_isSleeping.wait(
				true, 
				std::memory_order_acquire);
		}

		void remove_intent_to_sleep()
		{
			auto threadStatesOperation = m_scheduler.m_threadStatesSection.read();
			m_scheduler.wake_one_thread(threadStatesOperation, this);
		}

		void process_items(
			std::stop_token stopToken
		)
		{
			std::stop_callback
			{
				stopToken,
				[this]
				{
					m_isSleeping.exchange(false, std::memory_order_release);
					m_isSleeping.notify_all();
				}
			};

			while (!stopToken.stop_requested())
			{
				auto routine = acquire_local_item();
				if (!routine)
				{
					routine = acquire_remote_item();
				}
				if (!routine)
				{
					mark_intent_to_sleep();
					routine = acquire_remote_item();
					if (!routine)
					{
						sleep(
							stopToken);
					}
					remove_intent_to_sleep();
				}
				if (routine)
				{
					routine.resume();
				}
			}
		}
	};

	struct thread_state_list
	{
		std::unordered_map<std::thread::id, std::shared_ptr<thread_state>> m_threadStates;
	};

	std::atomic<size_t> m_sleepingThreadCount;
	read_copy_update_section<thread_state_list> m_threadStatesSection;
	typedef read_copy_update_section<thread_state_list>::read_operation thread_states_read_operation_type;
	typedef read_copy_update_section<thread_state_list>::update_operation thread_states_update_operation_type;

	std::shared_ptr<thread_state>& get_current_thread_state(
		thread_states_update_operation_type& threadStatesOperation
	)
	{
		auto iterator = threadStatesOperation->m_threadStates.find(
			std::this_thread::get_id());
		if (iterator != threadStatesOperation->m_threadStates.end())
		{
			return iterator->second;
		}

		auto threadState = std::make_shared<thread_state>(*this);
		do
		{
			threadStatesOperation.emplace(
				*threadStatesOperation
			);
			threadStatesOperation.replacement().m_threadStates[std::this_thread::get_id()] = threadState;
		} while (!threadStatesOperation.compare_exchange_strong());

		return threadStatesOperation->m_threadStates.find(
			std::this_thread::get_id()
		)->second;
	}

	void wake_one_thread(
		thread_states_read_operation_type& threadStatesOperation,
		thread_state* preferredThread = nullptr
	)
	{
		auto sleepingThreadCount = m_sleepingThreadCount.load(std::memory_order_acquire);
		do
		{
			if (sleepingThreadCount == 0)
			{
				return;
			}
		} while (!m_sleepingThreadCount.compare_exchange_weak(
			sleepingThreadCount,
			sleepingThreadCount - 1,
			std::memory_order_acquire,
			std::memory_order_relaxed
		));

		if (preferredThread
			&& preferredThread->try_wake())
		{
			return;
		}

		while (true)
		{
			for (auto& threadState : threadStatesOperation.value().m_threadStates)
			{
				if (threadState.second->try_wake())
				{
					return;
				}
			}
			threadStatesOperation.refresh();
		}
	}

	class awaiter
	{
		friend class thread_pool_scheduler;
		thread_pool_scheduler& m_scheduler;

		awaiter(
			thread_pool_scheduler& scheduler
		) : m_scheduler { scheduler }
		{}

	public:
		bool await_ready() const noexcept
		{
			return false;
		}

		void await_suspend(
			std::coroutine_handle<> continuation
		)
		{
			auto threadStatesOperation = m_scheduler.m_threadStatesSection.update();
			auto& threadState = m_scheduler.get_current_thread_state(threadStatesOperation);
			threadState->enqueue(continuation);
			m_scheduler.wake_one_thread(threadStatesOperation);
		}

		void await_resume() const noexcept
		{}
	};

public:
	awaiter operator co_await() noexcept
	{
		return awaiter{ *this };
	}

	void process_items(
		std::stop_token stopToken
	)
	{
		auto threadStatesOperation = m_threadStatesSection.update();
		auto threadState = get_current_thread_state(threadStatesOperation);
		threadState->process_items(
			stopToken
		);
	}
};

//inline thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_globalState;
//inline thread_local thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_threadState;

}
}