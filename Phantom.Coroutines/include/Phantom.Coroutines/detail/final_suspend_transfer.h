#pragma once

#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "Phantom.Coroutines/detail/coroutine.h"
#else
import Phantom.Coroutines.coroutine;
#endif
#include <assert.h>

namespace Phantom::Coroutines::detail
{

class final_suspend_transfer
{
    coroutine_handle<> m_continuation;
public:
    final_suspend_transfer(
        coroutine_handle<> continuation
    ) noexcept : m_continuation(
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