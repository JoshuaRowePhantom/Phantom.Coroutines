export module Phantom.Coroutines.async_manual_reset_event;

import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;

namespace Phantom::Coroutines
{

export class async_manual_reset_event
{
    class awaiter;
    struct SignalledState {};
    struct WaitingCoroutineState {};

    class awaiter
    {
        friend class async_manual_reset_event;

        union
        {
            awaiter* m_nextAwaiter;
            async_manual_reset_event* m_event;
        };

        coroutine_handle<> m_continuation;

        awaiter(
            async_manual_reset_event* event
        ) :
            m_event{ event }
        {}

    public:
        bool await_ready() const noexcept
        {
            // We can do a simple load to enable continuing manual reset
            // events in await_ready without having to do any exchange operations.
            return m_event->m_state.load(std::memory_order_acquire) == SignalledState{};
        }

        bool await_suspend(
            coroutine_handle<> continuation
        ) noexcept
        {
            auto nextStateLambda = [&](auto previousState) -> state_type
            {
                if (previousState == SignalledState{})
                {
                    return SignalledState{};
                }

                m_nextAwaiter = previousState.as<WaitingCoroutineState>();
                m_continuation = continuation;
                return this;
            };

            auto previousState = compare_exchange_weak_loop(
                m_event->m_state,
                nextStateLambda,
                std::memory_order_relaxed,
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
        StateSet<WaitingCoroutineState, awaiter*>
    > atomic_state_type;
    typedef state<atomic_state_type> state_type;
    static inline const state_type NotSignalledState = state_type{ nullptr };

    atomic_state_type m_state;

public:
    async_manual_reset_event(
        bool isSignalled = false
        ) noexcept
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

    awaiter operator co_await() noexcept
    {
        return awaiter{ this };
    }
};

}
