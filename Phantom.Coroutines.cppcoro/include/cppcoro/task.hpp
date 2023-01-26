#pragma once

#include "Phantom.Coroutines/awaiter_wrapper.h"
#include "Phantom.Coroutines/reusable_task.h"

namespace cppcoro
{
template<
    typename Result = void
> using task = ::Phantom::Coroutines::reusable_task<Result>;

}
