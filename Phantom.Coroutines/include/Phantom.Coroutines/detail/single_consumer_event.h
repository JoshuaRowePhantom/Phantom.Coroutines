#include "atomic_state.h"
#include "coroutine.h"
#include "immovable_object.h"

namespace Phantom::Coroutines
{
namespace detail
{

class single_consumer_event_states
{
public:
    struct NotSignalledState {};
    struct SignalledState {};
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<NotSignalledState>,
        SingletonState<SignalledState>,
        StateSet<WaitingCoroutineState, coroutine_handle<>>
    > atomic_state_type;
};

template<
    typename StateAfterResumeAwaiter
>
class single_consumer_event
    :
private immovable_object,
private single_consumer_event_states
{
    atomic_state_type m_atomicState;
    typedef state<atomic_state_type> state_type;

public:
    single_consumer_event(
        bool initiallySignalled = false
    ) : m_atomicState(
        initiallySignalled
        ?
        state_type{ SignalledState{} }
        :
        state_type{ NotSignalledState{} }
    )
    {}

#if 0
    ~single_consumer_auto_reset_event()
    {
        // This assertion seems like if would make sense,
        // but it's actually okay to destroy tasks that are suspended
        // while waiting for this event.
        assert(!m_atomicState.load(std::memory_order_acquire).is<WaitingCoroutineState>());
    }
#endif

    bool is_set() const
    {
        return m_atomicState.load(std::memory_order_acquire).is<SignalledState>();
    }

    void set()
    {
        auto nextStateLambda = [&](auto previousState) -> state_type
        {
            if (previousState.is<WaitingCoroutineState>())
            {
                return StateAfterResumeAwaiter{};
            }
            return SignalledState{};
        };

        auto previousState = compare_exchange_weak_loop(
            m_atomicState,
            nextStateLambda,
            std::memory_order_relaxed
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
        :
        private immovable_object
    {
        template<
            typename StateAfterResumeAwaiter
        > friend class single_consumer_event;

        single_consumer_event& m_event;

        awaiter(
            single_consumer_event& event
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
                return StateAfterResumeAwaiter{};
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

    awaiter operator co_await()
    {
        return awaiter{ *this };
    }
};

}
}
