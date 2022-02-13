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
    private event<true>
{
public:
    using event::event;
    using event::is_set;
    using event::reset;
    using event::operator co_await;

    void set()
    {
    }

};
}
using detail::auto_reset_event;
}
