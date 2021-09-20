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
struct as_future_promise;

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_awaitable
{
    typedef as_future_promise<TAwaitable, TResult> promise_type;
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_promise_base
{
    std::promise<TResult>& m_promise;
    typedef as_future_promise<TAwaitable, TResult> promise_type;

    auto get_coroutine_handle()
    {
        return coroutine_handle<promise_type>::from_promise(
            static_cast<promise_type&>(*this));
    }

    as_future_promise_base(
        std::promise<TResult>& promise,
        TAwaitable&
    ) :
        m_promise{ promise }
    {
    }

    ~as_future_promise_base()
    {

    }
    constexpr suspend_never initial_suspend() const noexcept { return suspend_never{}; }

    suspend_never final_suspend() noexcept
    {
        return suspend_never();
    }

    void unhandled_exception() noexcept
    {
        m_promise.set_exception(
            std::current_exception()
        );
    }

    as_future_awaitable<TAwaitable, TResult> get_return_object() noexcept
    {
        return as_future_awaitable<TAwaitable, TResult>{};
    }
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
struct as_future_promise
    :
public as_future_promise_base<
    TAwaitable,
    TResult
>
{
    using as_future_promise::as_future_promise_base::as_future_promise_base;

    template<
        typename TValue
    >
    void return_value(
        TValue&& value)
    {
        as_future_promise::as_future_promise_base::m_promise.set_value(
            std::forward<TValue>(value));
    }
};

template<
    is_awaitable TAwaitable
>
struct as_future_promise<
    TAwaitable,
    void
> :
public as_future_promise_base<
    TAwaitable,
    void
>
{
    using as_future_promise::as_future_promise_base::as_future_promise_base;
    
    void return_void()
    {
        as_future_promise::as_future_promise_base::m_promise.set_value();
    }
};

template<
    is_awaitable TAwaitable,
    typename TResult
>
as_future_awaitable<
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

template<
    is_awaitable TAwaitable
> auto as_future(
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

template<
    is_awaitable TAwaitable
> auto sync_wait(
    TAwaitable&& awaitable
)
{
    return (as_future(std::forward<TAwaitable>(awaitable)).get());
}

}

using detail::as_future;
using detail::sync_wait;

}