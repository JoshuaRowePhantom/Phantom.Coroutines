#include "detail/coroutine.h"
#include "detail/type_traits.h"
#include <exception>
#include <future>

namespace Phantom::Coroutines
{
namespace detail
{


template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_implementation_promise;

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_implementation_awaitable
{
    typedef as_future_implementation_promise<TAwaitable, TResult> promise_type;
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_implementation_promise_base
{
    std::promise<TResult>& m_promise;
    std::promise<TResult>& promise() { return m_promise; }

    typedef as_future_implementation_promise<TAwaitable, TResult> promise_type;

    auto get_coroutine_handle()
    {
        return coroutine_handle<promise_type>::from_promise(
            static_cast<promise_type&>(*this));
    }

    as_future_implementation_promise_base(
        std::promise<TResult>& promise,
        TAwaitable&
    ) :
        m_promise{ promise }
    {
    }

    constexpr suspend_never initial_suspend() const noexcept { return suspend_never{}; }
    constexpr suspend_never final_suspend() const noexcept { return suspend_never{}; }

    constexpr as_future_implementation_awaitable<TAwaitable, TResult> get_return_object() const noexcept
    {
        return as_future_implementation_awaitable<TAwaitable, TResult>{};
    }

    void unhandled_exception() noexcept
    {
        m_promise.set_exception(
            std::current_exception()
        );
    }
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_implementation_promise
    :
public as_future_implementation_promise_base<
    TAwaitable,
    TResult
>
{
    using as_future_implementation_promise::as_future_implementation_promise_base::as_future_implementation_promise_base;
    using as_future_implementation_promise::as_future_implementation_promise_base::promise;

    template<
        typename TValue
    >
    void return_value(
        TValue&& value)
    {
        promise().set_value(
            std::forward<TValue>(value));
    }
};

template<
    is_awaitable TAwaitable
>
struct as_future_implementation_promise<
    TAwaitable,
    void
> :
public as_future_implementation_promise_base<
    TAwaitable,
    void
>
{
    using as_future_implementation_promise::as_future_implementation_promise_base::as_future_implementation_promise_base;
    using as_future_implementation_promise::as_future_implementation_promise_base::promise;

    void return_void()
    {
        promise().set_value();
    }
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
as_future_implementation_awaitable<
    TAwaitable,
    TResult
>
as_future_implementation(
    std::promise<TResult>& promise,
    TAwaitable&& awaitable
)
{
    if constexpr (std::is_same_v<TResult, void>)
    {
        co_await awaitable;
    }
    else
    {
        co_return co_await awaitable;
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
        promise,
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