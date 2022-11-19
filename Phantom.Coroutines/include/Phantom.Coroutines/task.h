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
	public extensible_promise,
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
		this auto& self
	) noexcept
	{
		return suspend_always{};
	}

	auto final_suspend(
		this auto& self
	) noexcept
	{
		return final_suspend_transfer{ self.m_continuation };
	}

	auto get_return_object(
		this auto& self
	) noexcept
	{
		return task<Result>(
			self.handle()
			);
	}

	auto await_ready(
		this auto& self,
		auto& awaiter
	)
	{
		return false;
	}

	auto await_suspend(
		this auto& self,
		auto& awaiter,
		auto continuation
	)
	{
		self.m_continuation = continuation;
		return self.handle();
	}

	decltype(auto) await_resume(
		this auto& self,
		auto& awaiter
	)
	{
		if (self.m_result.index() == exception_index)
		{
			rethrow_exception(
				get<exception_index>(
					self.m_result)
			);
		}

		return self.return_result<result_index>(
			self.m_result);
	}

	void return_variant_result(
		this auto& self,
		auto&& value
	)
	{
		self.m_result.emplace<result_index>(
			std::forward<decltype(value)>(value));
	}

	void unhandled_exception(
		this auto& self
	)
	{
		self.m_result.emplace<exception_index>(
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
		coroutine_handle<Promise> handle
	) :
		extensible_awaitable<Promise>{ handle }
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

	bool await_ready(
		this auto& self
	) noexcept
	{
		return self.promise().await_ready(self);
	}

	auto await_suspend(
		this auto& self,
		auto awaiter
	) noexcept
	{
		return self.promise().await_suspend(self, awaiter);
	}

	decltype(auto) await_resume(
		this auto& self
	)
	{
		return self.promise().await_resume(self);
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

	task(coroutine_handle<Promise> handle)
		: task_awaitable<Promise>{ handle }
	{}

public:
	typedef Promise promise_type;

	task()
	{}

	auto operator co_await(
		this std::movable auto && self
		)
	{
		return task_awaiter<Promise>
		{
			std::move(self),
		};
	}
};

}

namespace Phantom::Coroutines
{
using detail::task;
using detail::task_awaiter;
using detail::task_promise;

}
