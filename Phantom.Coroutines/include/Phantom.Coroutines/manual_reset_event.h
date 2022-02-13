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
private event<true>
{
public:
    using event::event;
    using event::is_set;
    using event::reset;
    using event::operator co_await;

    void set()
    {
        auto previousState = m_state.exchange(SignalledState{});
        if (previousState.is<SignalledState>())
        {
            return;
        }
        auto signalledAwaiter = previousState.as<WaitingCoroutineState>();
        while (signalledAwaiter)
        {
            auto nextAwaiter = signalledAwaiter->m_nextAwaiter;
            signalledAwaiter->m_continuation.resume();
            signalledAwaiter = nextAwaiter;
        }
    }

};
}
using detail::manual_reset_event;
}
