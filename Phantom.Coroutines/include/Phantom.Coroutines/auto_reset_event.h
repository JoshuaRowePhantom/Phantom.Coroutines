#pragma once

#include <atomic>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/event.h"

namespace Phantom::Coroutines
{
namespace detail
{

class auto_reset_event
    :
    public event<false>
{
public:
    using event::event;
};
}
using detail::auto_reset_event;
}
