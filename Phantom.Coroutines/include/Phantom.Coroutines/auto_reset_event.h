#pragma once

#include <atomic>
#include "atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{

class auto_reset_event
{
    struct SignalledState {};
    struct WaitingCoroutineState;

public:
    class awaiter
    {
        friend class auto_reset_event;
        coroutine_handle<> m_coroutine;
        
        // Declare these members as a union to reduce memory usage.
        // We only need m_autoResetEvent before we've set m_nextAwaiter.
        union
        {
            awaiter* m_nextAwaiter;
            auto_reset_event* m_autoResetEvent;
        };

        awaiter(
            auto_reset_event* autoResetEvent
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
    auto_reset_event(
        bool initiallySignalled = false
    ) : m_atomicState(
        initiallySignalled
        ?
        state_type{ SignalledState{} }
        :
        NotSignalledState
    )
    {}

    ~auto_reset_event()
    {
        assert(!m_atomicState.load(std::memory_order_acquire).is<WaitingCoroutineState>());
    }

    bool is_set() const
    {
        return m_atomicState.load(std::memory_order_acquire).is<SignalledState>();
    }

    void set()
    {
        auto nextStateLambda = [&](state_type previousState) -> state_type
        {
            if (previousState.is<WaitingCoroutineState>())
            {
                return previousState.as<WaitingCoroutineState>()->m_nextAwaiter;
            }
            return SignalledState{};
        };

        auto previousState = compare_exchange_weak_loop(
            m_atomicState,
            nextStateLambda
        );

        if (previousState.is<WaitingCoroutineState>())
        {
            auto awaiter = previousState.as<WaitingCoroutineState>();
            awaiter->m_coroutine.resume();
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

bool auto_reset_event::awaiter::await_ready() noexcept
{
    auto previousState = m_autoResetEvent->m_atomicState.load(std::memory_order_relaxed);
    if (previousState != SignalledState{})
    {
        return false;
    }

    return m_autoResetEvent->m_atomicState.compare_exchange_strong(
        previousState,
        NotSignalledState,
        std::memory_order_acq_rel,
        std::memory_order_release
    );
}

inline bool auto_reset_event::awaiter::await_suspend(
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
            return NotSignalledState;
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

using detail::auto_reset_event;
}
