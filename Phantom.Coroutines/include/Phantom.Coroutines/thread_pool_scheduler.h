#pragma once

#include "detail/coroutine.h"
#include "scheduler.h"
#include "task.h"
#include <atomic>
#include <shared_mutex>
#include <unordered_set>
#include <unordered_map>
#include <vector>

namespace Phantom::Coroutines
{
namespace detail
{

class thread_pool_scheduler
{
	class awaiter;
	class thread_state;

	class awaiter_list
	{
		std::shared_mutex m_mutex;
		std::vector<awaiter*> m_waiters;
		size_t m_head = 0;
		size_t m_tail = 1;

		// Prevent implicit move and copy
		awaiter_list(
			awaiter_list&&
		) = delete;

	public:
		awaiter_list()
		{
		}

		void enqueue_from_this_thread(
			awaiter* waiter
		)
		{
			if (m_head - m_tail > m_waiters.size())
			{
				std::unique_lock lock(m_mutex);
				m_waiters.resize(
					(m_waiters.size() + 1) * 2
				);
			}

			m_waiters[m_head++ % m_waiters.size()] = waiter;
		}

		awaiter* dequeue_from_this_thread()
		{

		}
	};

	class thread_state :
		std::enable_shared_from_this<thread_state>
	{
		inline static std::shared_mutex m_globalStateMutex;
		inline static std::unordered_set<std::shared_ptr<thread_state>> m_globalThreadStates;
		
		static thread_local std::shared_ptr<thread_state> m_threadState;

		thread_pool_scheduler* m_scheduler = nullptr;
		awaiter_list m_waitersForThisScheduler;
		awaiter_list m_waitersForOtherSchedulers;
		size_t m_threadIndex;

	public:

		static thread_state& current()
		{
			if (!m_threadState)
			{
				m_threadState = std::make_shared<thread_state>();
				std::unique_lock lock{ m_globalStateMutex };
				m_globalThreadStates.insert(m_threadState);
			}

			return *m_threadState;
		}

		void enqueue(
			thread_pool_scheduler* scheduler,
			awaiter* waiter
		)
		{
			if (scheduler == m_scheduler)
			{
				m_waitersForThisScheduler.enqueue_from_this_thread(
					waiter
				);
			}
			else
			{
				m_waitersForOtherSchedulers.enqueue_from_this_thread(
					waiter
				);
			}
		}
	};
	
	class awaiter
	{
		friend class thread_state;
		friend class thread_pool_scheduler;

		coroutine_handle<> m_continuation;
		awaiter* m_nextAwaiter;
		thread_pool_scheduler* m_scheduler;

		awaiter(
			thread_pool_scheduler* scheduler
		) : 
			m_scheduler { scheduler }
		{}

	public:
		bool await_ready() const noexcept 
		{ 
			return false; 
		}

		void await_suspend(
			std::coroutine_handle<> continuation)
		{
			m_continuation = continuation;
			thread_state::current().enqueue(
				m_scheduler,
				this);
		}

		void await_resume() const noexcept
		{
		}
	};

public:

	awaiter operator co_await() noexcept
	{
		return awaiter{this};
	}
};

class thread_pool
{
public:
	task<> set_thread_count();
};

//inline thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_globalState;
//inline thread_local thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_threadState;

}
}