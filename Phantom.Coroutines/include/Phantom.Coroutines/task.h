#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "detail/promise_traits.h"
#include "detail/variant_result_storage.h"
#include "single_consumer_promise.h"
#include <concepts>
#include <exception>
#include <type_traits>
#include <variant>
#include "extensible_promise.h"

namespace Phantom::Coroutines::detail
{

template<
	typename Result = void,
	is_coroutine_handle Continuation = coroutine_handle<>
> class task_promise;

template<
	typename Result = void,
	typename Promise = task_promise<Result>
> class task;

template<
	typename Promise
> class task_awaiter;

template<
	typename Result,
	is_coroutine_handle Continuation
> class task_promise
	:
	public variant_return_result<Result>,
	private variant_result_storage<Result>
{
	using variant_result_storage<Result>::is_void;

	template<
		typename Result,
		typename Promise
	> friend class task;

	typedef std::variant<
		std::monostate,
		typename variant_result_storage<Result>::result_variant_member_type,
		std::exception_ptr
	> result_variant_type;

	result_variant_type m_result;
	static const size_t result_index = 1;
	static const size_t exception_index = 2;

	Continuation m_continuation;

public:
	typedef Result result_type;

	auto initial_suspend(
	) const noexcept
	{
		return suspend_always{};
	}

	auto final_suspend(
	) const noexcept
	{
		return final_suspend_transfer{ m_continuation };
	}

	auto get_return_object(
	) noexcept
	{
		return task<Result> { *this };
	}

	auto continue_with(
		auto continuation
	)
	{
		m_continuation = continuation;
		return coroutine_handle<task_promise>::from_promise(*this);
	}

	decltype(auto) await_resume()
	{
		if (m_result.index() == exception_index)
		{
			rethrow_exception(
				get<exception_index>(
					m_result)
			);
		}

		return this->return_result<result_index>(
			m_result);
	}

	void return_variant_result(
		auto&& value
	)
	{
		m_result.emplace<result_index>(
			std::forward<decltype(value)>(value));
	}

	void unhandled_exception()
	{
		m_result.emplace<exception_index>(
			std::current_exception());
	}
};

template<
	typename Promise
> class task_awaitable
	:
public extensible_awaitable<Promise>
{
protected:
	task_awaitable(
	)
	{}

	task_awaitable(
		Promise& promise
	) :
		extensible_awaitable<Promise>{ promise }
	{}

	task_awaitable(
		task_awaitable&& other
	) :
		extensible_awaitable<Promise>{ std::move(other) }
	{
		other.handle() = nullptr;
	}

public:
	task_awaitable& operator=(
		task_awaitable&& other
		)
	{
		if (this->handle())
		{
			this->handle().destroy();
		}
		this->handle() = other.handle();
		other.handle() = nullptr;
	}

	~task_awaitable()
	{
		if (this->handle())
		{
			this->handle().destroy();
		}
	}
};

template<
	typename Promise
> class task_awaiter 
	:
task_awaitable<Promise>
{
	template<
		typename Result,
		typename Promise
	> friend class task;

	task_awaiter(
		task_awaitable<Promise>&& other
	) :
		task_awaitable<Promise>{ std::move(other) }
	{}

public:

	bool await_ready() const noexcept
	{
		return false;
	}

	auto await_suspend(
		auto awaiter
	) noexcept
	{
		return this->promise().continue_with(awaiter);
	}

	decltype(auto) await_resume(
	)
	{
		return this->promise().await_resume();
	}
};

template<
	typename Result,
	typename Promise
> class task
	:
	task_awaitable<Promise>
{
	template<
		typename Result,
		is_coroutine_handle Continuation
	> friend class task_promise;

	task(Promise& promise)
		: task_awaitable<Promise>{ promise }
	{}

public:
	typedef Promise promise_type;

	task()
	{}

	auto operator co_await(
		)
	{
		return task_awaiter<Promise>
		{
			std::move(*this),
		};
	}
};

}

namespace Phantom::Coroutines
{
using detail::task;
using detail::task_awaiter;
using detail::task_promise;

static_assert(detail::is_awaiter<task_awaiter<task_promise<>>>);
static_assert(std::same_as<task_promise<>, std::coroutine_traits<task<>>::promise_type>);
static_assert(std::same_as<task_awaiter<task_promise<>>, awaiter_type<task<>>>);
static_assert(detail::has_co_await_member<task<>>);
static_assert(detail::is_awaitable<task<>>);

}
