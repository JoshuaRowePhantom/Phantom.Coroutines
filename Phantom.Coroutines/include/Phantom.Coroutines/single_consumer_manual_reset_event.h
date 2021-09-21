#pragma once

#include <atomic>
#include "detail/atomic_state.h"
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
    > atomic_state_type;

    atomic_state_type m_atomicState;
    typedef state<atomic_state_type> state_type;
public:
    single_consumer_manual_reset_event(
        bool initiallySignalled = false
    ) : m_atomicState(
        initiallySignalled
        ?
        state_type{ SignalledState{} }
        :
        state_type{ NotSignalledState{} }
    )
    {}

    ~single_consumer_manual_reset_event()
    {
        assert(!m_atomicState.load(std::memory_order_acquire).is<WaitingCoroutineState>());
    }

    bool is_set() const
    {
        return m_atomicState.load(std::memory_order_acquire).is<SignalledState>();
    }

    void set()
    {
        auto previousState = m_atomicState.exchange(
            state_type{ SignalledState{} },
            std::memory_order_acq_rel
        );

        if (previousState.is<WaitingCoroutineState>())
        {
            auto coroutine = previousState.as<WaitingCoroutineState>();
            coroutine.resume();
        }
    }

    void reset()
    {
        state_type expectedState = SignalledState{};

        // If the state was Signalled, it becomes NotSignalled.
        // If the state was NotSignalled, it stays that way.
        // If the state was WaitingCoroutine, it stays that way.
        m_atomicState.compare_exchange_strong(
            expectedState,
            NotSignalledState{},
            std::memory_order_acq_rel,
            std::memory_order_acquire);
    }

    class awaiter
    {
        friend class single_consumer_manual_reset_event;
        single_consumer_manual_reset_event& m_event;

        awaiter(
            single_consumer_manual_reset_event& event
        ) :
            m_event
        {
            event
        }
        {}

    public:
        bool await_ready() noexcept
        {
            return m_event.m_atomicState.load(std::memory_order_acquire) == SignalledState{};
        }

        bool await_suspend(
            coroutine_handle<> coroutine
        ) noexcept
        {
            auto nextStateLambda = [&](auto previousState) -> state_type
            {
                if (previousState == NotSignalledState{})
                {
                    return coroutine;
                }
                return SignalledState{};
            };

            auto previousState = compare_exchange_weak_loop(
                m_event.m_atomicState,
                nextStateLambda,
                std::memory_order_relaxed
            );

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

    awaiter operator co_await() { return awaiter{ *this }; }
};

}
using detail::single_consumer_manual_reset_event;
}
