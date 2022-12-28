#pragma once

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