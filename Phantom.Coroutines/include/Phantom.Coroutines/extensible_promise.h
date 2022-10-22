#pragma once

#include <concepts>
#include <type_traits>
#include "type_traits.h"
#include "detail/awaiter_wrapper.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{
struct extensible_promise_args_constructor_tag;
struct extensible_promise_default_constructor_tag;
template<
	typename T
> struct base_promise_tag {};

template<
	typename ExtendedPromise,
	typename Promise
> concept is_extended_promise_of = requires(ExtendedPromise promise)
{
	{ promise.template promise<Promise>() } -> std::same_as<Promise&>;
};

template<
	typename Promise
> struct wrapper_promise_return
{
	decltype(auto) return_value(
		this auto& self,
		auto&&... value
	)
	{
		return self->return_value(
			std::forward<decltype(value)>(value)...);
	}
};

template<
	has_return_void Promise
> struct wrapper_promise_return<
	Promise
>
{
	decltype(auto) return_void(
		this auto& self,
		auto&&... value
	)
	{
		return self->return_void(
			std::forward<decltype(value)>(value)...);
	}
};

// A derived_promise is a promise that wraps another promise type
// by derivation.
template<
	typename Promise
> class derived_promise
	:
	public Promise
{
	struct BasePromiseTag {};
protected:
	typedef Promise base_promise_type;

	decltype(auto) base_promise()
	{
		return *this;
	}

public:
	// These constructors allow the derived promise
	// to always provide a constructor and delegate to
	// derived_promise's constructor,
	// without regard as to whether the base promise
	// provides a constructor.
	// 
	// A derived promise can also use a using declaration
	// to import derived_promise's constructors.

	// Enable construction by delegating the arguments
	// to the promise object.
	// This constructor is enabled only if the promise object
	// supports the argument set.
	template<
		typename ... Args
	> derived_promise(
		Args&&... args
	)
		requires std::constructible_from<Promise, Args&&...>
	:
	Promise(
		std::forward<Args>(args)...
	)
	{}

	// Enable construction by delegating the arguments
	// to the promise object.
	// This constructor is enabled only if the promise object
	// does not support the argument set and default-constructs
	// the promise.
	template<
		typename ... Args
	> derived_promise(
		Args&&... args
	)
		requires !std::constructible_from<Promise, Args&&...>
	:
	Promise()
	{}
};

// An extensible_promise is a promise type that can
// be extended or wrapped by other promise types.
class extensible_promise
{
public:
	auto handle(
		this auto& self
	) noexcept
	{
		return std::coroutine_handle<
			std::remove_cv_t<decltype(self)>
		>::from_promise(self);
	}
};

// An extensible awaitable is an awaitable object that can reference
// an extensible promise.
template<
	typename Promise
> class extensible_awaitable
{
public:
	using promise_type = Promise;
	using coroutine_handle_type = coroutine_handle<promise_type>;

private:
	coroutine_handle<promise_type> m_coroutineHandle;

protected:
	extensible_awaitable(
		Promise& promise
	) :
		m_coroutineHandle{ coroutine_handle_type::from_promise(promise) }
	{}

	extensible_awaitable(
		coroutine_handle_type coroutineHandle = nullptr
	) :
		m_coroutineHandle { coroutineHandle }
	{}

	decltype(auto) handle()
	{
		return (m_coroutineHandle);
	}

	promise_type& promise() const
	{
		return m_coroutineHandle.promise();
	}
};

template<
	typename Promise,
	is_awaitable Awaitable
> class extended_awaiter;

template<
	typename Awaitable,
	typename Promise
> constexpr bool is_extended_awaiter_v = false;

template<
	typename Promise,
	is_awaitable BaseAwaitable
> constexpr bool is_extended_awaiter_v<
	extended_awaiter<Promise, BaseAwaitable>,
	Promise
> = true;

template<
	typename Awaitable,
	typename Promise
> concept is_extended_awaiter = is_extended_awaiter_v<Awaitable, Promise>;

template<
	typename Promise,
	is_awaitable Awaitable
> class extended_awaiter
	:
public awaiter_wrapper<Awaitable>
{
	template<
		typename Promise,
		is_awaitable Awaitable
	> friend class extended_awaiter;

	std::coroutine_handle<Promise> m_handle;

protected:

	template<
		typename AwaitableArg
	>
	extended_awaiter(
		Promise& promise,
		AwaitableArg&& awaitable
	) : 
		awaiter_wrapper<Awaitable>{ std::forward<AwaitableArg>(awaitable) },
		m_handle { std::coroutine_handle<Promise>::from_promise(promise) }
	{}

	std::coroutine_handle<Promise> handle() const noexcept
	{
		return m_handle;
	}

	Promise& promise() const noexcept
	{
		return handle().promise();
	}
};

// This specialization uses the awaitable object's handle() method
// to retrieve the handle, instead of storing the handle directly,
// thus optimizing an extended_awaiter wrapping another extended_awaiter.
template<
	typename Promise,
	is_extended_awaiter<Promise> Awaitable
> class extended_awaiter<
	Promise,
	Awaitable
>
	:
	public awaiter_wrapper<Awaitable>
{
	template<
		typename Promise,
		is_awaitable Awaitable
	> friend class extended_awaiter;

protected:

	template<
		typename AwaitableArg
	>
	extended_awaiter(
		Promise& promise,
		AwaitableArg&& awaitable
	) :
		// Delegate to awaiter_wrapper
		awaiter_wrapper<Awaitable>{ std::forward<AwaitableArg>(awaitable) }

		// Discard the "promise" argument, since it will have been stored
		// in the target awaiter.
	{}

	std::coroutine_handle<Promise> handle() const noexcept
	{
		return this->awaiter().handle();
	}

	Promise& promise() const noexcept
	{
		return handle().promise();
	}
};

}
}
