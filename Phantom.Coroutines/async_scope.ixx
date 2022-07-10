export module Phantom.Coroutines.async_scope;

import <atomic>;
import <exception>;
import Phantom.Coroutines.coroutine;

import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.type_traits;

namespace Phantom::Coroutines
{

export class async_scope
{
	std::atomic<size_t> m_outstandingTasks = 1;
	coroutine_handle<> m_continuation;
	coroutine_handle<> m_coroutineToDestroy;

	class join_awaiter
	{
		friend class async_scope;

		async_scope& m_asyncScope;

		join_awaiter(
			async_scope& asyncScope
		) : 
			m_asyncScope { asyncScope }
		{}

	public:
		bool await_ready() const noexcept 
		{ 
			return false; 
		}

		bool await_suspend(
			coroutine_handle<> continuation
		) noexcept
		{
			m_asyncScope.m_continuation = continuation;
			if (m_asyncScope.m_outstandingTasks.fetch_sub(1, std::memory_order_acquire) == 1)
			{
				return false;
			}
			return true;
		}

		void await_resume() 
		{
			if (m_asyncScope.m_coroutineToDestroy)
			{
				m_asyncScope.m_coroutineToDestroy.resume();
			}
		}
	};

	class promise;
	class future
	{
	public:
		typedef promise promise_type;
	};

	class promise
	{
		async_scope& m_asyncScope;

	public:
		promise(
			async_scope& asyncScope,
			auto& awaiter
		) :
			m_asyncScope{ asyncScope }
		{}

		~promise()
		{
		}

		suspend_never initial_suspend() const noexcept
		{
			return suspend_never{};
		}

		future get_return_object()
		{
			return future{};
		}

		void return_void()
		{
		}

		void unhandled_exception() noexcept
		{
			std::terminate();
		}
	
		suspend_never final_suspend() noexcept
		{
			return suspend_never{};
		}
	};

	// Implemented here instead of promise::final_suspend due to bug in code gen for symmetric transfer.
	struct join_resumer
	{
		async_scope& m_asyncScope;

		bool await_ready() const noexcept
		{
			return false;
		}

		coroutine_handle<> await_suspend(
			coroutine_handle<> coroutineToDestroy
		) noexcept
		{
			m_asyncScope.m_coroutineToDestroy = coroutineToDestroy;
			return m_asyncScope.m_continuation;
		}

		void await_resume() const noexcept 
		{
		}
	};

	future await_impl(
		is_awaitable auto&& awaiter
	)
	{
		co_await std::forward<decltype(awaiter)>(awaiter);
		if (m_outstandingTasks.fetch_sub(1) == 1)
		{
			co_await join_resumer{ *this };
		}
	}

public:
	void spawn(
		is_awaitable auto&& awaiter
		)
	{
		m_outstandingTasks.fetch_add(
			1, 
			std::memory_order_relaxed);

		await_impl(
			std::forward<decltype(awaiter)>(awaiter)
		);
	}

	join_awaiter join()
	{
		return join_awaiter{ *this };
	}
};

}
