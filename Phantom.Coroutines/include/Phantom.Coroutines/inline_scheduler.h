#ifndef PHANTOM_COROUTINES_INCLUDE_INLINE_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_INLINE_SCHEDULER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/coroutine.h"
#include "scheduler.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
class inline_scheduler
{
public:
    suspend_never schedule() noexcept 
    { 
        return suspend_never{}; 
    }
};

static_assert(is_scheduler<inline_scheduler>);

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::inline_scheduler;

}
#endif
