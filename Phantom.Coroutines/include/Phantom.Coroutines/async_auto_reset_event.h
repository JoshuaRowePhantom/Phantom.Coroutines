#pragma once

#include <atomic>
#include "double_wide_atomic.h"
#include "detail/coroutine.h"
#include "policies.h"

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
class basic_async_auto_reset_event;

template<
    typename T
> concept is_async_auto_reset_event_policy =
is_concrete_policy<T, await_is_not_cancellable>
// Technically, we have no special support for failing on destroy with awaiters yet,
// but the user-visible functionality is identical to noop in release builds.
|| is_concrete_policy<T, noop_on_destroy>
|| is_concrete_policy<T, fail_on_destroy_with_awaiters>
// Technically, we have no special support for single awaiters yet,
// but the user-visible functionality is identical to multi awaiters.
|| is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>;

template<
    is_async_auto_reset_event_policy ... Policy
> using async_auto_reset_event = basic_async_auto_reset_event<
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
> class basic_async_auto_reset_event
{
    struct state_type
    {
        size_t m_waitingCount = 0;
        size_t m_setCount = 0;
    };

    class awaiter;

    // Awaiters that have been pulled from the m_state variable
    // and that should be resumed before those in the m_state variable.
    std::atomic<awaiter*> m_pendingAwaiters = nullptr;
    std::atomic<double_wide_value<state_type>> m_state;
    awaiter* m_unservicedAwaiters = nullptr;
    awaiter** m_unservicedAwaitersTail = &m_unservicedAwaiters;

    void resume_awaiters(
        double_wide_value<state_type> previousState
    )
    {
        auto fetchCount = std::min(
            previousState->m_setCount, 
            previousState->m_waitingCount);
        awaiter* waitersToService = nullptr;

        /*

Resume_FetchListenersToService:
    while FetchingCount # 0 do
        assert ~Destroyed;
*/
        while (fetchCount)
        {
            /*
        \* This requires a single atomic exchange of EnqueuedListeners
        FetchedListeners := EnqueuedListeners;
        EnqueuedListeners := << >>;

        */
            auto fetchedWaiters = m_pendingAwaiters.exchange(
                nullptr,
                std::memory_order_acquire);

            /*
Resume_DecrementCounts_and_AdjustLists:
        assert ~Destroyed;
        ListenersToService := ListenersToService \o
            SubSeq(
                UnservicedListeners \o FetchedListeners,
                1,
                FetchingCount)
        ||
        UnservicedListeners := SubSeq(
            UnservicedListeners \o FetchedListeners,
            FetchingCount + 1,
            Len(UnservicedListeners \o FetchedListeners));

        FetchedListeners := << >>;
        */

        // fetchedWaiters is in reverse order of delivery,
        // so reverse it and append to m_unservicedAwaiters
            awaiter* unservicedAwaiters = nullptr;
            auto newTail = &fetchedWaiters->m_nextAwaiter;
            while (fetchedWaiters)
            {
                auto next = fetchedWaiters->m_nextAwaiter;
                fetchedWaiters->m_nextAwaiter = unservicedAwaiters;
                unservicedAwaiters = fetchedWaiters;
                *m_unservicedAwaitersTail = fetchedWaiters;
                fetchedWaiters = next;
            }
            m_unservicedAwaitersTail = newTail;

            // Now iterate forward through m_unservicedAwaiters
            // to move fetchCount items to our local set to service.
            // Note that this changes the order, but this is within contract
            // as the multiple overlapping set / wait operations
            // can be delivered in any order.
            for (size_t counter = 0; counter < fetchCount; ++counter)
            {
                auto next = m_unservicedAwaiters->m_nextAwaiter;
                m_unservicedAwaiters->m_nextAwaiter = waitersToService;
                waitersToService = m_unservicedAwaiters;
                m_unservicedAwaiters = next;
                if (m_unservicedAwaiters == nullptr)
                {
                    m_unservicedAwaitersTail = &m_unservicedAwaiters;
                }
            }

            /*
        */
        /*
        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        SetCount := SetCount - FetchingCount;
        WaiterCount := WaiterCount - FetchingCount;
        if SetCount > 0 /\ WaiterCount > 0 then
            FetchingCount := Min({ SetCount, WaiterCount });
        else
            FetchingCount := 0;
        end if;
        */
            double_wide_value<state_type> nextState;
            do
            {
                nextState = previousState;
                nextState->m_setCount -= fetchCount;
                nextState->m_waitingCount -= fetchCount;
            } while (!m_state.compare_exchange_weak(
                previousState,
                nextState));

            fetchCount = std::min(
                nextState->m_setCount,
                nextState->m_waitingCount);
        /*
    end while;
    */
        }
        /*
Resume_SignalListeners:
    while ListenersToService # << >> do
        ListenerStates[Head(ListenersToService)] := "Complete";
        ListenersToService := Tail(ListenersToService);
    end while;
    return;
end procedure;
        */
        
        // Now all the pending awaiters are in waitersToService
        while (waitersToService)
        {
            auto next = waitersToService->m_nextAwaiter;
            if (waitersToService->m_referenceCount.fetch_sub(1, std::memory_order_acquire) == 1)
            {
                waitersToService->m_continuation.resume();
            }
            waitersToService = next;
        }
    }

    // This class follows the algorithm in AutoResetEvent_v2.tla
    class awaiter
    {
        friend class basic_async_auto_reset_event;

        union
        {
            awaiter* m_nextAwaiter;
            basic_async_auto_reset_event* m_event;
        };

        Continuation m_continuation;
        std::atomic<char> m_referenceCount = 2;

        awaiter(
            basic_async_auto_reset_event* event
        ) :
            m_event{ event }
        {}

    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        coroutine_handle<> await_suspend(
            Continuation continuation
        ) noexcept
        {
            /*
        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        await SetCount > WaiterCount;
        SetCount := SetCount - 1;
        ListenerStates[self] := "Complete";
            */
            // We replace m_event with an awaiter pointer in this method,
            // so hold onto event locally.
            auto event = m_event;

            double_wide_value previousState = event->m_state.load_inconsistent();
            
            // Try once to resume with a single compare-exchange.
            auto nextState = previousState;
            if (nextState->m_setCount > nextState->m_waitingCount)
            {
                nextState->m_setCount--;
                if (event->m_state.compare_exchange_weak(
                    previousState,
                    nextState))
                {
                    return continuation;
                }
            }

            /*

Listen_EnqueueWaiter:
        EnqueuedListeners := EnqueuedListeners \o << self >>;
        ListenerStates[self] := "Waiting";
*/
            m_continuation = continuation;
            m_nextAwaiter = event->m_pendingAwaiters;
            while (!event->m_pendingAwaiters.compare_exchange_weak(
                m_nextAwaiter,
                this,
                std::memory_order_acq_rel
            ))
            {
            }

/*
Listen_IncrementWaiterCount:
        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        WaiterCount := WaiterCount + 1;
        if SetCount > 0 /\ WaiterCount = 1 then
            call ResumeAwaiters(
                Min({ SetCount, WaiterCount }));
        end if;
            */
            do
            {
                nextState = previousState;
                nextState->m_waitingCount++;
            } while (!event->m_state.compare_exchange_weak(
                previousState,
                nextState));

            if (nextState->m_setCount > 0
                && nextState->m_waitingCount == 1)
            {
                event->resume_awaiters(
                    nextState);
            }

            if (m_referenceCount.fetch_sub(1, std::memory_order_acquire) == 1)
            {
                return continuation;
            }

            return noop_coroutine();
        }

        void await_resume(
        ) const noexcept
        {
        }
    };

public:
    basic_async_auto_reset_event(
        bool isSignalled = false
        )
        :
        m_state
        { {
            .m_waitingCount = 0,
            .m_setCount = isSignalled ? size_t(1) : size_t(0),
        } }
    {
    }

    bool is_set() const noexcept
    {
        auto state = m_state.load();
        return state->m_setCount > state->m_waitingCount;
    }

    void set() noexcept
    {
        /*

        \* Set is a noop when SetCount >= WaiterCount + 1
        \* This action requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        await SetCount < WaiterCount + 1;
        SetCount := Min({SetCount + 1, WaiterCount + 1});
        if SetCount = 1 /\ WaiterCount > 0 then
            call ResumeAwaiters(
                Min({ SetCount, WaiterCount }));
            goto Set;
        end if;

        */
        double_wide_value<state_type> previousState = m_state.load_inconsistent();
        double_wide_value<state_type> nextState;
        do
        {
            nextState = previousState;
            nextState->m_setCount = std::min(
                nextState->m_setCount + 1, 
                nextState->m_waitingCount + 1);
        } while (!m_state.compare_exchange_weak(
            previousState, 
            nextState));

        if (nextState->m_setCount == 1
            && nextState->m_waitingCount > 0)
        {
            resume_awaiters(
                nextState);
        }
    }

    void reset() noexcept
    {
        /*
            await SetCount > WaiterCount;
            SetCount := SetCount - 1;
        */

        double_wide_value<state_type> previousState = m_state.load_inconsistent();
        double_wide_value<state_type> nextState;
        do
        {
            nextState = previousState;
            if (nextState->m_setCount > nextState->m_waitingCount)
            {
                nextState->m_setCount--;
            }
        } while (!m_state.compare_exchange_weak(
            previousState,
            nextState));
    }

    awaiter operator co_await()
    {
        return awaiter{ this };
    }
};

}
using detail::async_auto_reset_event;
}
