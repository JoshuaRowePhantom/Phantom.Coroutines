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

class final_suspend_transfer_and_destroy
    :
public final_suspend_transfer
{
public:
    final_suspend_transfer_and_destroy(
        coroutine_handle<> continuation
    ) : final_suspend_transfer(
        continuation
    )
    {
    }

    coroutine_handle<> await_suspend(
        coroutine_handle<> coroutine
    ) const noexcept
    {
        auto continuation = final_suspend_transfer::await_suspend(
            coroutine);

        // Calling destroy will probably destroy the state in this instance,
        // since it was allocated in the frame of the coroutine we're destroying.
        // So make sure we do it after we've retrieve the continuation.
        coroutine.destroy();

        return continuation;
    }

};

}