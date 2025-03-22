#ifndef PHANTOM_COROUTINES_INCLUDE_ASYNC_MANUAL_RESET_EVENT_H
#define PHANTOM_COROUTINES_INCLUDE_ASYNC_MANUAL_RESET_EVENT_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include "policies.h"
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#endif

#include "detail/assert_is_configured_module.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_concrete_policy<await_is_not_cancellable> AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy
>
class basic_async_manual_reset_event;

template<
    typename T
> concept is_async_manual_reset_event_policy =
is_concrete_policy<T, await_is_not_cancellable>
|| is_await_result_on_destruction_policy<T>
|| is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>;

template<
    is_async_manual_reset_event_policy ... Policy
> using async_manual_reset_event = basic_async_manual_reset_event<
    select_await_cancellation_policy<Policy..., await_is_not_cancellable>,
    select_continuation_type<Policy..., default_continuation_type>,
    select_awaiter_cardinality_policy<Policy..., multiple_awaiters>,
    select_await_result_on_destruction_policy<Policy..., noop_on_destroy>
>;

template<
    is_concrete_policy<await_is_not_cancellable> AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy
> class basic_async_manual_reset_event
{
    // Since there is no user-visible behavior change except in debug builds,
    // we support single_awaiter cardinality, so don't explicitly require it here.
    // static_assert(std::is_base_of_v<multiple_awaiters, AwaiterCardinalityPolicy>);
    static_assert(
        std::is_base_of_v<noop_on_destroy, AwaitResultOnDestructionPolicy>
        ||
        std::is_base_of_v<fail_on_destroy_with_awaiters, AwaitResultOnDestructionPolicy>
        );

    class awaiter;
    struct SignalledState {};
    struct WaitingCoroutineState {};

    class awaiter
    {
        friend class basic_async_manual_reset_event;

        union
        {
            awaiter* m_nextAwaiter;
            basic_async_manual_reset_event* m_event;
        };

        coroutine_handle<> m_continuation;

        awaiter(
            basic_async_manual_reset_event* event
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
    basic_async_manual_reset_event(
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

    awaiter operator co_await() const noexcept
    {
        return awaiter{ const_cast<basic_async_manual_reset_event*>(this) };
    }
};

}
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::async_manual_reset_event;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_async_manual_reset_event_policy;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_async_manual_reset_event;
}
#endif
