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
		}

		void await_resume() const noexcept
		{
		}
	};

	std::atomic<awaiter*> m_awaiters;

public:
	awaiter operator co_await() noexcept
	{
		return awaiter{this};
	}
};

//inline thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_globalState;
//inline thread_local thread_pool_scheduler::thread_state thread_pool_scheduler::thread_state::m_threadState;

}
}