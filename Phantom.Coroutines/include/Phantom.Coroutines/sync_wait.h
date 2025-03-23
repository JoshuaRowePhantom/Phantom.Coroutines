#ifndef PHANTOM_COROUTINES_INCLUDE_SYNC_WAIT_H
#define PHANTOM_COROUTINES_INCLUDE_SYNC_WAIT_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <exception>
#include <future>
#include "detail/config.h"
#include "detail/coroutine.h"
#include "type_traits.h"
#ifdef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#include "task.h"
#include <optional>
#endif
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

struct as_future_implementation_promise;

struct as_future_implementation_awaitable
{
    typedef as_future_implementation_promise promise_type;
};

struct as_future_implementation_promise
{
    constexpr suspend_never initial_suspend() const noexcept 
    { 
        return suspend_never{}; 
    }

    constexpr suspend_never final_suspend() const noexcept 
    {
        return suspend_never{}; 
    }

    constexpr as_future_implementation_awaitable get_return_object() const noexcept
    {
        return as_future_implementation_awaitable{};
    }

    constexpr void return_void() noexcept
    {
    }

    constexpr void unhandled_exception() noexcept
    {
        assert(false);
    }
};

template<
    typename T
> struct as_future_promise_type;

template<
    is_awaitable Awaitable
> struct as_future_promise_type<
    Awaitable
>
{
    using result_type =
        std::conditional_t<
        std::is_rvalue_reference_v<awaitable_result_type_t<Awaitable>>,
        std::remove_reference_t<awaitable_result_type_t<Awaitable>>,
        awaitable_result_type_t<Awaitable>
        >;
    using promise_type = std::promise<result_type>;
};

template<
    std::invocable Invocable
> struct as_future_promise_type<
    Invocable
> :
public as_future_promise_type<
    std::invoke_result_t<Invocable>
>
{
};

template<
    std::invocable TInvocable,
    typename promise_type = as_future_promise_type<TInvocable>::promise_type
>
as_future_implementation_awaitable
as_future_implementation(
    promise_type promise,
    TInvocable&& invocable
)
requires is_awaitable<std::invoke_result_t<TInvocable>>
{
    TInvocable invoked{ invocable };

    try
    {
        if constexpr (std::is_same_v<std::promise<void>, promise_type>)
        {
            co_await invoked();
            promise.set_value();
        }
        else
        {
            promise.set_value(
                co_await invoked());
        }
    }
    catch (...)
    {
        promise.set_exception(
            std::current_exception()
        );
    }
}

// Given a lambda returning an awaitable object, return an std::future representing it.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    std::invocable TInvocable
> auto as_future(
    TInvocable&& invocable
)
requires is_awaitable<std::invoke_result_t<TInvocable>>
{
    typename as_future_promise_type<TInvocable>::promise_type promise;
    auto future = promise.get_future();

    as_future_implementation(
        std::move(promise),
        std::forward<TInvocable>(invocable));

    return future;
}

// Given an awaitable object, return an std::future representing it.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_awaitable TAwaitable
> auto as_future(
    TAwaitable&& awaitable
)
{
    return as_future(
        [&]() -> decltype(auto) 
        { 
            return std::forward<TAwaitable>(awaitable); 
        }
    );
}

// Synchronously wait for the result of an awaitable object and return its result.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_awaitable TAwaitable
> decltype(auto) sync_wait(
    TAwaitable&& awaitable
)
{
    typedef decltype(
        as_future(
            std::forward<TAwaitable>(awaitable)
        ).get()) result_type;

#if PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE

    // Bug https://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239

    if constexpr (
        !std::is_void_v<result_type>
        &&
        !std::is_reference_v<result_type>
        &&
        !std::is_trivially_constructible_v<result_type>
        &&
        !is_optional<result_type>)
    {
        auto wrapWithOptional = [&]() -> task<std::optional<result_type>>
        {
            co_return co_await std::forward<TAwaitable>(awaitable);
        };

        return static_cast<result_type>(
            *as_future(wrapWithOptional()).get());
    }
    else
#endif
    {
        return static_cast<result_type>(
            as_future(std::forward<TAwaitable>(awaitable)).get());
    }
}

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::as_future;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::sync_wait;

}
#endif
