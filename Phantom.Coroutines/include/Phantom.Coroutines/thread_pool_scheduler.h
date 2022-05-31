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
			size_t m_mask;

			void resize(
				size_t size
			)
			{
				m_continuations.resize(
					std::bit_ceil(size)
				);
				m_mask = m_continuations.size() - 1;
			}

		public:
			queue(
				size_t size = 16
			)
			{
				resize(size);
			}

			size_t size()
			{
				return m_continuations.size();
			}

			coroutine_handle<>& operator[](size_t index)
			{
				return m_continuations[index & m_mask];
			}
			
			queue grow(
				size_t requiredSize,
				size_t outstandingCopyOperationCount,
				size_t currentTail,
				size_t currentHead
			)
			{
				queue result(requiredSize);
				for (auto index = currentTail - outstandingCopyOperationCount; index != currentHead; index++)
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
		enum class ProcessingState
		{
			// The thread is inside a call to process_items,
			// and hasn't been stopped.
			Processing,
			// The thread is sleeping.
			Sleeping,
			// The thread has been requested to stop while it is sleeping.
			Sleeping_StopRequested,
			// The thread has been requested to stop while it is processing.
			Processing_StopRequested,
			// The thread has stopped processing, or hasn't started.
			Stopped
		};
		std::atomic<ProcessingState> m_processingState = ProcessingState::Stopped;

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
						outstandingCopyOperationCount,
						tail,
						m_head.load(std::memory_order_relaxed)
					)
				);
				queueOperation.exchange();
			}

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
			auto processingState = m_processingState.load(std::memory_order_acquire);
			
			bool wasSleeping =
				processingState == ProcessingState::Sleeping
				|| processingState == ProcessingState::Sleeping_StopRequested;

			auto nextState = ProcessingState::Processing;
			if (processingState == ProcessingState::Sleeping_StopRequested)
			{
				nextState = ProcessingState::Processing_StopRequested;
			}

			bool doWakeThread = wasSleeping && m_processingState.compare_exchange_strong(
				processingState,
				nextState,
				std::memory_order_relaxed,
				std::memory_order_acquire
			);
			
			if (doWakeThread)
			{
				m_processingState.notify_all();
			}

			return doWakeThread;
		}

		coroutine_handle<> acquire_local_item()
		{
			auto head = m_head.load(std::memory_order_relaxed);
			// Special case, since head is unsigned
			if (head == 0) { return coroutine_handle<>{}; }
			auto newHead = head - 1;
			m_head.store(newHead, std::memory_order_release);

			auto tail = m_tail.load(std::memory_order_acquire);
			if (tail > newHead)
			{
				std::scoped_lock lock{ m_mutex };
				tail = m_tail.load(std::memory_order_acquire);
				if (tail > newHead)
				{
					m_head.store(head, std::memory_order_release);
					return coroutine_handle<>{};
				}
			}

			auto coroutine = copy_and_invalidate(
				(*m_queueReadCopyUpdateSection)[newHead]
			);
			assert_is_valid(coroutine);
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
			// We can't steal from ourselves!
			if (&other == this)
			{
				return coroutine_handle<>{};
			}

			std::unique_lock lock{ other.m_mutex, std::defer_lock };
			if (stealMode == steal_mode::Precise)
			{
				lock.lock();
			}

			auto otherTail = other.m_tail.load(std::memory_order_acquire);
			auto otherHead = other.m_head.load(std::memory_order_acquire);
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

				otherHead = other.m_head.load(std::memory_order_acquire);
				otherTail = other.m_tail.load(std::memory_order_acquire);
				if (otherHead <= otherTail)
				{
					return coroutine_handle<>{};
				}
			}

			// We are here, that means we can legitimately steal.
			// We steal half (rounded up) of the items in the source thread.
			size_t sizeToSteal = (otherHead - otherTail + 1) / 2;
			other.m_outstandingCopyOperationCount.fetch_add(
				sizeToSteal,
				std::memory_order_relaxed
			);
			auto newOtherTail = otherTail + sizeToSteal;
			other.m_tail.store(newOtherTail, std::memory_order_release);

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
				
				// As the new value is strictly smaller than the old value, this can be "relaxed".
				other.m_outstandingCopyOperationCount.fetch_sub(
					sizeToSteal,
					std::memory_order_relaxed
				);

				return std::coroutine_handle<>{};
			} else if (newOtherHead < newOtherTail)
			{
				// We have to give back some of the items.
				// We'll again target taking 1/2 of the items in the queue, rounded up.
				auto newSizeToSteal = (newOtherHead - otherTail + 1) / 2;
				auto countToGiveBack = sizeToSteal - newSizeToSteal;
				newOtherTail = otherTail + newSizeToSteal;
				
				other.m_tail.store(newOtherTail, std::memory_order_release);

				// As the new value is strictly smaller than the old value, this can be "relaxed".
				other.m_outstandingCopyOperationCount.fetch_sub(countToGiveBack, std::memory_order_relaxed);

				sizeToSteal = newSizeToSteal;
			}

			// We no longer need the lock.
			// We've reserved enough space in the queue via m_outstandingCopyOperationCount that
			// we can start a read only queue operation in the source to copy the items
			// into our queue.
			lock.unlock();

			// It's important to grab the otherQueueOperation -after- we have acquired other.m_head,
			// as other.m_head releases the queue update operation.
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
				auto coroutine = copy_and_invalidate((*otherQueueOperation)[otherTail + itemCounter]);

				assert_is_valid(coroutine);

				(*thisQueueOperation)[head + itemCounter] = coroutine;
			}

			// This releases all the copy operations done above.
			m_head.store(newHead, std::memory_order_release);

			auto itemToProcess = copy_and_invalidate((*otherQueueOperation)[otherTail + sizeToSteal - 1]);
			assert_is_valid(itemToProcess);

			// Need not be release, as the value will be strictly smaller than what it was before.
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
			auto previousProcessingState = m_processingState.load(
				std::memory_order_acquire
			);

			if (previousProcessingState == ProcessingState::Sleeping_StopRequested
				|| previousProcessingState == ProcessingState::Processing_StopRequested)
			{
				return;
			}

			m_processingState.compare_exchange_strong(
				previousProcessingState,
				ProcessingState::Sleeping
			);

			bool wasSleeping = previousProcessingState == ProcessingState::Sleeping;
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

			m_processingState.wait(
				ProcessingState::Sleeping,
				std::memory_order_acquire);
		}

		void remove_intent_to_sleep()
		{
			auto threadStatesOperation = m_scheduler.m_threadStatesSection.read();
			m_scheduler.wake_one_thread(threadStatesOperation, this);
		}

		void mark_intent_to_stop_processing()
		{
			auto previousState = m_processingState.load(
				std::memory_order_relaxed
			);
			while (true)
			{
				auto nextState = ProcessingState::Processing_StopRequested;
				if (previousState == ProcessingState::Sleeping)
				{
					nextState = ProcessingState::Sleeping_StopRequested;
				}

				if (m_processingState.compare_exchange_weak(
					previousState,
					nextState,
					std::memory_order_release,
					std::memory_order_relaxed
				))
				{
					break;
				}
			}
			m_processingState.notify_all();
		}

		void process_items(
			std::stop_token stopToken
		)
		{
			std::stop_callback stopCallback
			{
				stopToken,
				[this]
				{
					mark_intent_to_stop_processing();
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

	std::shared_ptr<thread_state> get_current_thread_state()
	{
		auto threadStatesOperation = m_threadStatesSection.update();
		auto threadState = get_current_thread_state(threadStatesOperation);
		return threadState;
	}

	void await_suspend(
		std::coroutine_handle<> continuation
	)
	{
		auto threadStatesOperation = m_threadStatesSection.update();
		auto& threadState = get_current_thread_state(threadStatesOperation);
		threadState->enqueue(continuation);
		wake_one_thread(threadStatesOperation);
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
			m_scheduler.await_suspend(continuation);
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
		auto threadState = get_current_thread_state();
		threadState->process_items(
			stopToken
		);
	}
};

//inline thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_globalState;
//inline thread_local thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_threadState;

}
}