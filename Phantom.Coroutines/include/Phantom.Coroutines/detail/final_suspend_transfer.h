#include "coroutine.h"

namespace Phantom::Coroutines::detail
{

class final_suspend_transfer
{
    coroutine_handle<> m_continuation;
public:
    final_suspend_transfer(
        coroutine_handle<> continuation
    ) : m_continuation(
        continuation
    )
    {}

    constexpr bool await_ready() const noexcept { return false; }

    constexpr coroutine_handle<> await_suspend(
        coroutine_handle<>
    ) const noexcept
    {
        return m_continuation;
    }

    constexpr void await_resume() const noexcept {}
};

template<
    typename TPromise
>
class final_suspend_transfer_and_destroy
    :
public final_suspend_transfer
{
public:
    final_suspend_transfer_and_destroy(
        TPromise& promise,
        coroutine_handle<> continuation
    ) : final_suspend_transfer
    {
        continuation
    }
    {
        coroutine_handle<TPromise>::from_promise(promise).destroy();
    }
};

}