#include "Phantom.Coroutines/detail/coroutine.h"

namespace Phantom::Coroutines::detail
{

// These types are used as placeholders in tests.
template<
    typename TResumeResult,
    typename TSuspendResult = void
>
struct typed_awaiter
{
    bool await_ready();
    TSuspendResult await_suspend(coroutine_handle<>);
    TResumeResult await_resume();
};

template<
    typename TResumeResult,
    typename TSuspendResult = void,
    typename TRValueResultResult = TResumeResult
> struct typed_awaitable
{
    typed_awaiter<TResumeResult, TSuspendResult> operator co_await() &;
    typed_awaiter<TRValueResultResult, TSuspendResult> operator co_await() &&;
};

struct not_awaitable
{};
}
