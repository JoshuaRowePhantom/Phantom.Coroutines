#pragma once

#include <atomic>
#include "atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{

class manual_reset_event
{
    struct SignalledState {};
    struct WaitingCoroutineState;

public:
    class awaiter
    {
        friend class manual_reset_event;
        coroutine_handle<> m_coroutine;
        
        // Declare these members as a union to reduce memory usage.
        // We only need m_autoResetEvent before we've set m_nextAwaiter.
        union
        {
            awaiter* m_nextAwaiter;
            manual_reset_event* m_autoResetEvent;
        };

        awaiter(
            manual_reset_event* autoResetEvent
        ) :
            m_autoResetEvent{
                autoResetEvent
        }
        {}

    public:
        awaiter(const awaiter&) = delete;
        void operator=(const awaiter&) = delete;

        inline bool await_ready() noexcept;

        inline bool await_suspend(
            coroutine_handle<> coroutine
        ) noexcept;

        inline void await_resume() noexcept {}
    };

private:

    typedef atomic_state<
        SingletonState<SignalledState>,
        StateSet<WaitingCoroutineState, awaiter*>
    > atomic_state_type;

    atomic_state_type m_atomicState;
    typedef state<atomic_state_type> state_type;

    static inline const state_type NotSignalledState = nullptr;

public:
    manual_reset_event(
        bool initiallySignalled = false
    ) : m_atomicState(
        initiallySignalled
        ?
        state_type{ SignalledState{} }
        :
        NotSignalledState
    )
    {}

    ~manual_reset_event()
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
            NotSignalledState
        );

        if (previousState == SignalledState{})
        {
            return;
        }

        auto awaiter = previousState.as<WaitingCoroutineState>();

        while (awaiter)
        {
            auto nextAwaiter = awaiter->m_nextAwaiter;
            awaiter->m_coroutine.resume();
            awaiter = nextAwaiter;
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
            state_type{ nullptr },
            std::memory_order_acq_rel,
            std::memory_order_acquire);
    }
};

bool manual_reset_event::awaiter::await_ready() noexcept
{
    auto previousState = m_autoResetEvent->m_atomicState.load(std::memory_order_acquire);
    return previousState == SignalledState{};
}

inline bool manual_reset_event::awaiter::await_suspend(
    coroutine_handle<> coroutine
) noexcept
{
    // We have to copy this locally because we reset the union member during
    // nextStateLambda.
    auto autoResetEvent = m_autoResetEvent;
    m_coroutine = coroutine;

    auto nextStateLambda = [&](state_type previousState) -> state_type
    {
        if (previousState == SignalledState{})
        {
            return SignalledState{};
        }

        // This erases any value we had for m_autoResetEvent
        m_nextAwaiter = previousState.as<WaitingCoroutineState>();
        
        return this;
    };

    auto previousState = compare_exchange_weak_loop(
        autoResetEvent->m_atomicState,
        nextStateLambda
    );

    return previousState == SignalledState{};
}

}

using detail::manual_reset_event;
}
