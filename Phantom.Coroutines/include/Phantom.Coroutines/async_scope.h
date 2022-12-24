#pragma once

#include <atomic>
#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "policies.h"
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_await_cancellation_policy AwaitCancellationPolicy,
	is_continuation Continuation,
	is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
	is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
	is_use_after_join_policy AwaitAfterJoinPolicy
>
class basic_async_scope;

template<
	typename T
> concept is_async_scope_policy =
is_await_cancellation_policy<T>
|| is_await_result_on_destruction_policy<T>
|| is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>;

template<
	is_async_scope_policy ... Policy
> using async_scope = basic_async_scope<
	select_await_cancellation_policy<Policy..., await_is_not_cancellable>,
	select_continuation_type<Policy..., default_continuation_type>,
	select_awaiter_cardinality_policy<Policy..., single_awaiter>,
	select_await_result_on_destruction_policy<Policy..., noop_on_destroy>,
	select_use_after_join_policy<Policy..., fail_on_use_after_join>
>;

template<
	is_await_cancellation_policy AwaitCancellationPolicy,
	is_continuation Continuation,
	is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
	is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
	is_use_after_join_policy AwaitAfterJoinPolicy
>
class basic_async_scope
{
	std::atomic<size_t> m_outstandingTasks = 1;
	coroutine_handle<> m_continuation;
	coroutine_handle<> m_coroutineToDestroy;

	class join_awaiter
	{
		friend class basic_async_scope;

		basic_async_scope& m_asyncScope;

		join_awaiter(
			basic_async_scope& asyncScope
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
		basic_async_scope& m_asyncScope;

	public:
		promise(
			basic_async_scope& asyncScope,
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
		basic_async_scope& m_asyncScope;

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
		std::invocable<> auto function
	)
	{
		co_await std::invoke(function);
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
		return spawn(
			[&awaiter]() -> decltype(auto)
			{
				return std::forward<decltype(awaiter)>(awaiter);
			});
	}

	void spawn(
		std::invocable<> auto&& function
	)
	{
		m_outstandingTasks.fetch_add(
			1,
			std::memory_order_relaxed);

		await_impl(
			std::forward<decltype(function)>(function)
		);
	}

	join_awaiter join()
	{
		return join_awaiter{ *this };
	}
};

}
using detail::async_scope;
}