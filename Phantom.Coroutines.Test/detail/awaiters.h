#include <coroutine>
#include <functional>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.coroutine;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/coroutine.h"
#endif

namespace Phantom::Coroutines::detail
{

// These types are used as placeholders in tests.
template<
    typename TResumeResult,
    typename TSuspendResult = void
>
struct typed_awaiter
{
    bool await_ready() { std::unreachable(); }
    TSuspendResult await_suspend(coroutine_handle<>) { std::unreachable(); }
    TResumeResult await_resume() { std::unreachable(); }
};

template<
    typename TResumeResult,
    typename TSuspendResult = void,
    typename TRValueResultResult = TResumeResult
> struct typed_awaitable
{
    typed_awaiter<TResumeResult, TSuspendResult> operator co_await()& { std::unreachable(); }
    typed_awaiter<TRValueResultResult, TSuspendResult> operator co_await() && { std::unreachable(); }
};

struct not_awaitable
{};

template<
    typename AwaitSuspendResult = void,
    typename AwaitResumeResult = void
>
struct generic_awaiter
{
    bool m_awaitReadyResult = false;
    std::function<AwaitSuspendResult(coroutine_handle<>)> m_awaitSuspendResult;
    std::function<AwaitResumeResult()> m_awaitResumeResult;

    bool m_awaitReadyCalled = false;
    bool m_awaitSuspendCalled = false;
    bool m_awaitResumeCalled = false;
    coroutine_handle<> m_suspendedHandle;
    
    bool await_ready()
    {
        m_awaitReadyCalled = true;
        return m_awaitReadyResult;
    }

    auto await_suspend(
        coroutine_handle<> handle
    )
    {
        m_awaitSuspendCalled = true;
        m_suspendedHandle = handle;
        return m_awaitSuspendResult(
            handle);
    }

    decltype(auto) await_resume()
    {
        m_awaitResumeCalled = true;
        return m_awaitResumeResult();
    }
};

template<
    typename AwaitSuspendResult = void,
    typename AwaitResumeResult = void
>
struct generic_awaitable_lvalue
{
    generic_awaiter<AwaitSuspendResult, AwaitResumeResult> m_awaiter;

    auto& operator co_await() &
    {
        return m_awaiter;
    }
};

template<
    typename AwaitSuspendResult = void,
    typename AwaitResumeResult = void
>
struct generic_awaitable_rvalue
{
    generic_awaiter<AwaitSuspendResult, AwaitResumeResult> m_awaiter;

    decltype(auto) operator co_await() &&
    {
        return std::move(m_awaiter);
    }
};

template<
    typename AwaitSuspendResult = void,
    typename AwaitResumeResult = void
>
struct generic_awaitable_value
{
    generic_awaiter<AwaitSuspendResult, AwaitResumeResult> m_awaiter;

    auto operator co_await()
    {
        return m_awaiter;
    }
};

struct unusable_promise;
struct unusable_task
{
    typedef unusable_promise promise_type;
    coroutine_handle<> m_coroutine;

    unusable_task(
        coroutine_handle<> coroutine
    )
        : m_coroutine { coroutine }
    {
    }

    unusable_task(
        unusable_task&& other
    ) noexcept
    {
        m_coroutine = other.m_coroutine;
        other.m_coroutine = coroutine_handle<>{};
    }

    ~unusable_task()
    {
        if (m_coroutine)
        {
            m_coroutine.destroy();
        }
    }
};

struct unusable_promise
{
    unusable_task get_return_object() noexcept
    {
        return unusable_task(
            coroutine_handle<unusable_promise>::from_promise(*this)
        );
    }

    void unhandled_exception() noexcept
    {}

    void return_void() noexcept
    {}

    suspend_always initial_suspend() const noexcept
    {
        return {};
    }

    suspend_always final_suspend() const noexcept
    {
        return {};
    }
};

inline unusable_task get_unusable_task()
{
    co_return;
}

}
