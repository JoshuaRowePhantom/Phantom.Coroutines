#ifndef PHANTOM_COROUTINES_INCLUDE_INLINE_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_INLINE_SCHEDULER_H
#include "scheduler.h"

namespace Phantom::Coroutines
{
namespace detail
{

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

using detail::inline_scheduler;

}
#endif
