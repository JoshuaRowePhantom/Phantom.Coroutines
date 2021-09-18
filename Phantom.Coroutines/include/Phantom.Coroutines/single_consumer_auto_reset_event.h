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
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<NotSignalledState>,
        SingletonState<SignalledState>,
        StateSet<WaitingCoroutineState, coroutine_handle<>>
    > atomic_state_type;

    atomic_state_type m_state;
    typedef state<atomic_state_type> state_type;
public:
    single_consumer_auto_reset_event(
        bool initiallySignalled = false
    ) : m_state(
        initiallySignalled 
        ? 
        state_type{ SignalledState{} }
        : 
        state_type{ NotSignalledState{} }
    )
    {}

    ~single_consumer_auto_reset_event()
    {
        assert(
            m_state.load() == SignalledState{}
            || m_state.load() == NotSignalledState{});
    }

    bool is_set() const
    {
        return m_state.load(std::memory_order_acquire).is<SignalledState>();
    }

    void set()
    {
        state_type expectedState = m_state.load(
            std::memory_order_relaxed);
        
        state_type nextState = SignalledState{};

        do
        {
            if (expectedState.is<WaitingCoroutineState>())
            {
                nextState = NotSignalledState{};
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
        state_type expectedState = SignalledState{};

        // If the state was Signalled, it becomes NotSignalled.
        // If the state was NotSignalled, it stays that way.
        // If the state was WaitingCoroutine, it stays that way.
        m_state.compare_exchange_strong(
            expectedState,
            NotSignalledState{},
            std::memory_order_acq_rel,
            std::memory_order_acquire);
    }

    bool await_ready() noexcept
    {
        return m_state.load(std::memory_order_acquire) == SignalledState{};
    }

    bool await_suspend(
        coroutine_handle<> coroutine
    ) noexcept
    {
        state_type previousState = m_state.load(
            std::memory_order_acquire
        );

        state_type newState = coroutine;

        do
        {
            if (previousState == SignalledState{})
            {
                newState = NotSignalledState{};
            }
            else
            {
                newState = coroutine;
            }
        }
        while (!m_state.compare_exchange_strong(
            previousState,
            coroutine,
            std::memory_order_acq_rel,
            std::memory_order_acquire
        ));

        if (previousState == SignalledState{})
        {
            return false;
        }

        // If there is another coroutine handle,
        // then this object isn't being used as expected;
        // there's only supposed to be a single consumer ever doing
        // co_await operations.
        assert(previousState == NotSignalledState{});

        return true;
    };

    void await_resume() noexcept
    {
    }
};

}
using detail::single_consumer_auto_reset_event;
}
