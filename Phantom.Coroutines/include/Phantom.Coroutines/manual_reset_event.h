#pragma once

#include <atomic>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/event.h"

namespace Phantom::Coroutines
{
namespace detail
{

class manual_reset_event
    :
    public event<true>
{
public:
    using event::event;
};
}
using detail::manual_reset_event;
}
