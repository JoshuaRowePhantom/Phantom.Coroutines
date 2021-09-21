#include "detail/coroutine.h"
#include "detail/type_traits.h"
#include <exception>
#include <future>

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
    constexpr suspend_never initial_suspend() const noexcept { return suspend_never{}; }
    constexpr suspend_never final_suspend() const noexcept { return suspend_never{}; }

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
            co_await awaitable;
            promise.set_value();
        }
        else
        {
            promise.set_value(
                co_await awaitable);
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
    typedef awaitable_result_type_t<TAwaitable> result_type;

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
    return (as_future(std::forward<TAwaitable>(awaitable)).get());
}

}

using detail::as_future;
using detail::sync_wait;

}