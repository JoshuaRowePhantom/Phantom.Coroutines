#pragma once

#include <atomic>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{

class auto_reset_event
{
    class awaiter;
    struct SignalledState {};
    struct SignallingState {};
    struct WaitingCoroutineState {};

    class awaiter
    {
        friend class event;
        friend class manual_reset_event;
        friend class auto_reset_event;

        union
        {
            awaiter* m_nextAwaiter;
            auto_reset_event* m_event;
        };

        coroutine_handle<> m_continuation;

        awaiter(
            auto_reset_event* event
        ) :
            m_event{ event }
        {}

    public:
        bool await_ready() const noexcept
        {
            // We can do a simple load to enable continuing manual reset
            // events in await_ready without having to do any exchange operations;
            // auto reset event has to atomically set the state to NotSignalled,
            // so we always return false for it.
            return false;
        }

        bool await_suspend(
            coroutine_handle<> continuation
        ) noexcept
        {
            auto nextStateLambda = [&](auto previousState) -> state_type
            {
                if (previousState == SignalledState{})
                {
                    return NotSignalledState;
                }

                m_nextAwaiter = previousState.as<WaitingCoroutineState>();
                m_continuation = continuation;
                return this;
            };

            auto previousState = compare_exchange_weak_loop(
                m_event->m_state,
                nextStateLambda,
                std::memory_order_acquire,
                std::memory_order_release,
                std::memory_order_acquire
            );

            return previousState != SignalledState{};
        }

        void await_resume() const noexcept
        {
        }
    };

    typedef atomic_state<
        SingletonState<SignalledState>,
        SingletonState<SignallingState>,
        StateSet<WaitingCoroutineState, awaiter*>
    > atomic_state_type;
    typedef state<atomic_state_type> state_type;

    static inline const state_type NotSignalledState = state_type{ nullptr };

    atomic_state_type m_state;
    std::atomic<size_t> m_pendingSets;

public:
    auto_reset_event(
        bool isSignalled = false
        )
        :
        m_state{ isSignalled ? state_type{SignalledState{}} : NotSignalledState }
    {
    }

    bool is_set() const noexcept
    {
        return m_state.load(std::memory_order_acquire) == SignalledState{};
    }

    void set() noexcept
    {

    }

    void reset() noexcept
    {
        state_type signalled = SignalledState{};

        // If the state is signalled, sets it to not signalled.
        // If the state is not signalled, stays not signalled.
        // If the state is that there is a waiter (and therefore not signalled), stays with a waiter.
        m_state.compare_exchange_strong(
            signalled,
            NotSignalledState);
    }

    awaiter operator co_await()
    {
        return awaiter{ this };
    }
};

}
using detail::auto_reset_event;
}
