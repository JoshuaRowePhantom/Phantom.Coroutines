#pragma once

#include <atomic>
#include "atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{
class single_consumer_auto_reset_event
{
    struct NotSignalledState {};
    struct SignalledState {};

    typedef atomic_state<
        SingletonState<NotSignalledState>,
        SingletonState<SignalledState>,
        StateSet<coroutine_handle<>>
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
            if (expectedState.is<coroutine_handle<>>())
            {
                nextState = NotSignalledState();
            }

        } while (!m_state.compare_exchange_weak(
            expectedState,
            nextState,
            std::memory_order_acq_rel,
            std::memory_order_relaxed));

        if (expectedState.is<coroutine_handle<>>())
        {
            auto coroutine = expectedState.as<coroutine_handle<>>();
            coroutine.resume();
        }
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
