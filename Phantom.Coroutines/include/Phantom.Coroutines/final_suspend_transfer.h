#ifndef PHANTOM_COROUTINES_INCLUDE_FINAL_SUSPEND_TRANSFER_H
#define PHANTOM_COROUTINES_INCLUDE_FINAL_SUSPEND_TRANSFER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include "Phantom.Coroutines/detail/coroutine.h"
#include "Phantom.Coroutines/detail/config_macros.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
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
#endif
