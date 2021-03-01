#pragma once

#include <atomic>
#include "atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{
class single_consumer_manual_reset_event
{
    struct NotSignalledState {};
    struct SignalledState {};
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<NotSignalledState>,
        SingletonState<SignalledState>,
        StateSet<WaitingCoroutineState, coroutine_handle<>>
    > state_type;

    state_type m_state;

public:
    single_consumer_auto_reset_event(
        bool initiallySignalled = false
    ) : m_state(
        initiallySignalled ? state<state_type>(SingletonState<SignalledState>()) : NotSignalledState()
    )
    {}

    void set()
    {
        state<state_type> expectedState = m_state.load(
            std::memory_order_relaxed);
        
        state<state_type> nextState = SignalledState();

        do
        {
            if (expectedState.is<WaitingCoroutineState>())
            {
                nextState = NotSignalledState();
            }

        } while (!m_state.compare_exchange_weak(
            expectedState,
            nextState,
            std::memory_order_acq_rel,
            std::memory_order_relaxed));

        if (expectedState.is<WaitingCoroutineState>())
        {
            auto coroutine = expectedState.as<WaitingCoroutineState>();
            coroutine.resume();
        }
    }

    void reset()
    {
        state<state_type> expectedState = SignalledState();

        // If the state was Signalled, it becomes NotSignalled.
        // If the state was NotSignalled, it stays that way.
        // If the state was WaitingCoroutine, it stays that way.
        m_state.compare_exchange_strong(
            expectedState,
            NotSignalledState(),
            std::memory_order_acq_rel,
            std::memory_order_acquire);
    }

    class awaiter
    {
        friend class single_consumer_auto_reset_event;

        awaiter(
            single_consumer_auto_reset_event& event
        );

    public:
        bool await_ready() noexcept;
        coroutine_handle<> await_suspend(coroutine_handle<>) noexcept;
        void await_resume() noexcept;
    };

    awaiter operator co_await();
};

}
using detail::single_consumer_auto_reset_event;
}
