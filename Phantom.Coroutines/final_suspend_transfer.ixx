export module Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.coroutine;
import <assert.h>;

namespace Phantom::Coroutines
{

export class final_suspend_transfer
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

    constexpr void await_resume() const noexcept 
    {
        // This line of code should be impossible to hit.
        assert(false);
    }
};
}