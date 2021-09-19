#include "detail/coroutine.h"
#include <exception>
#include <future>

namespace Phantom::Coroutines
{
namespace detail
{


template<
    typename TAwaitable,
    typename TResult
>
struct as_future_awaitable
{
    typedef TResult result_type;

    struct promise_type
    {
        std::promise<result_type> m_promise;

        promise_type(
            std::promise<result_type>& promise,
            TAwaitable&
        ) :
            m_promise{ std::move(promise) }
        {}

        suspend_never initial_suspend() const { return suspend_never{}; }

        suspend_never final_suspend() const
        {
            coroutine_handle<promise_type>::from_promise(*this).destroy();
            return suspend_never();
        }

        void unhandled_exception() noexcept
        {
            m_promise.set_exception(
                std::current_exception()
            );
        }

        void return_void()
        {
            m_promise.set_value();
        }

        template<
            typename TValue
        >
            void return_value(
                TValue&& value)
        {
            m_promise.set_value(
                std::forward<TValue>(value));
        }
    };


};

template<
    typename TAwaitable
> auto as_future(
    TAwaitable&& awaitable
)
{
    typedef void result_type;

    auto lambda = [&](
        auto promise,
        TAwaitable&& awaitable
        ) -> as_future_awaitable<result_type>
    {
        co_await awaitable;
    };

    std::promise<result_type> promise;
    auto future = promise.get_future();

    lambda(
        promise,
        std::forward<TAwaitable>(awaitable));

    return future;
}

template<
    typename TAwaitable
> auto sync_wait(
    TAwaitable&& awaitable
)
{
    return (as_future(awaitable).get());
}

}

using detail::as_future;
using detail::sync_wait;

}