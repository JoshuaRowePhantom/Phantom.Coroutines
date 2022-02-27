#pragma once

#include "detail/coroutine.h"
#include "detail/type_traits.h"
#include <exception>
#include <future>
#ifdef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#include "task.h"
#include <optional>
#endif

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
    is_awaitable TAwaitable,
    typename TResult
>
as_future_implementation_awaitable
as_future_implementation(
    std::promise<TResult> promise,
    TAwaitable&& awaitable
)
{
    try
    {
        if constexpr (std::is_same_v<TResult, void>)
        {
            co_await std::forward<TAwaitable>(awaitable);
            promise.set_value();
        }
        else
        {
            promise.set_value(
                co_await std::forward<TAwaitable>(awaitable));
        }
    }
    catch (...)
    {
        promise.set_exception(
            std::current_exception()
        );
    }
}

// Given an awaitable object, return an std::future representing it.
template<
    is_awaitable TAwaitable
> decltype(auto) as_future(
    TAwaitable&& awaitable
)
{
    typedef std::conditional_t<
        std::is_rvalue_reference_v<awaitable_result_type_t<TAwaitable>>,
        std::remove_reference_t<awaitable_result_type_t<TAwaitable>>,
        awaitable_result_type_t<TAwaitable>
    > result_type;

    std::promise<result_type> promise;
    auto future = promise.get_future();

    as_future_implementation(
        std::move(promise),
        std::forward<TAwaitable>(awaitable));

    return future;
}

// Synchronously wait for the result of an awaitable object and return its result.
template<
    is_awaitable TAwaitable
> decltype(auto) sync_wait(
    TAwaitable&& awaitable
)
{
    typedef awaitable_result_type_t<TAwaitable> awaitable_result_type;
        typedef std::conditional_t<
        std::is_rvalue_reference_v<awaitable_result_type>,
        std::remove_reference_t<awaitable_result_type>,
        awaitable_result_type
    > result_type;

#ifdef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE

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

        return static_cast<result_type>(*as_future(wrapWithOptional()).get());
    }
    else
#endif
    {
        return static_cast<result_type>(as_future(std::forward<TAwaitable>(awaitable)).get());
    }
}

}

using detail::as_future;
using detail::sync_wait;

}