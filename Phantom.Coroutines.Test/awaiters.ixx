export module Phantom.Coroutines.Test.awaiters;
import Phantom.Coroutines.coroutine;

namespace Phantom::Coroutines
{

// These types are used as placeholders in tests.
export template<
    typename TResumeResult,
    typename TSuspendResult = void
>
struct typed_awaiter
{
    bool await_ready();
    TSuspendResult await_suspend(coroutine_handle<>);
    TResumeResult await_resume();
};

export template<
    typename TResumeResult,
    typename TSuspendResult = void,
    typename TRValueResultResult = TResumeResult
> struct typed_awaitable
{
    typed_awaiter<TResumeResult, TSuspendResult> operator co_await() &;
    typed_awaiter<TRValueResultResult, TSuspendResult> operator co_await() &&;
};

export struct not_awaitable
{};
}
