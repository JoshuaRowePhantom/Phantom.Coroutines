#pragma once

#include <atomic>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "policies.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy
>
class basic_async_auto_reset_event;

template<
    typename T
> concept is_async_auto_reset_event_policy =
is_await_cancellation_policy<T>
|| is_await_result_on_destruction_policy<T>
// It might appear that allowing only a single awaiter for a mutex
// wouldn't be useful, but actually it is:
// a common case is that there only two threads of control vying
// for the mutex, and therefore only one of them can be awaiting.
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
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy
>
class basic_async_auto_reset_event
{
    // This class follows the algorithm in AutoResetEvent.tla

    class awaiter;
    struct SignalledState {};
    struct SignallingState {};
    struct WaitingCoroutineState {};
    struct NoWaitingCoroutineState {};

    class awaiter
    {
        friend class basic_async_auto_reset_event;

        union
        {
            awaiter* m_nextAwaiter;
            basic_async_auto_reset_event* m_event;
        };

        coroutine_handle<> m_continuation;

        awaiter(
            basic_async_auto_reset_event* event
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
/*
Listen_Start(thread) ==
        /\  ListeningThreadPCs[thread] = "Idle"
        /\  \/  /\  State.Type = "Signalled"
                /\  State' = [State EXCEPT !.Type = "NoWaitingCoroutine" ]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Resume"]
                /\  UNCHANGED << NextAwaiters >>
            \/  /\  State.Type = "NoWaitingCoroutine"
                /\  State' = [ Type |-> "WaitingCoroutine", Thread |-> << thread >>]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Pending"]
                /\  UNCHANGED << NextAwaiters >>
            \/  /\  State.Type \in { "WaitingCoroutine", "Signalling" }
                /\  State' = [State EXCEPT !.Thread = << thread >> ]
                /\  NextAwaiters' = [NextAwaiters EXCEPT ![thread] = State.Thread]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Pending"]
        /\  UNCHANGED << SignallingThreadPCs, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
*/
                if (previousState == SignalledState{})
                {
                    return NoWaitingCoroutineState{};
                }

                m_continuation = continuation;
                
                if (previousState == NoWaitingCoroutineState{})
                {
                    m_nextAwaiter = nullptr;
                    return state_type{ WaitingCoroutineState{}, this };
                }
/*
            \/  /\  State.Type \in { "WaitingCoroutine", "Signalling" }
                /\  State' = [State EXCEPT !.Thread = << thread >> ]
                /\  NextAwaiters' = [NextAwaiters EXCEPT ![thread] = State.Thread]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Pending"]
                /\  UNCHANGED << PendingSignalCount >>
*/
                if (previousState.is<WaitingCoroutineState>())
                {
                    m_nextAwaiter = previousState.as<WaitingCoroutineState>();
                    return state_type{ WaitingCoroutineState{}, this };
                }

                assert(previousState.is<SignallingState>());

                m_nextAwaiter = previousState.as<SignallingState>();
                return state_type{ SignallingState{}, this };
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
        SingletonState<NoWaitingCoroutineState>,
        StateSet<WaitingCoroutineState, awaiter*>,
        StateSet<SignallingState, awaiter*>
    > atomic_state_type;
    typedef state<atomic_state_type> state_type;

    atomic_state_type m_state;
    std::atomic<size_t> m_pendingSets;

    // Awaiters that have been pulled from the m_state variable
    // and that should be resumed before those in the m_state variable.
    awaiter* m_pendingAwaiters = nullptr;

    void obtainPendingAwaiters(
        state_type& lastState
    )
    {
        /*
Signal_ObtainPendingAwaiters(thread) ==
        /\  SignallingThreadPCs[thread] \in {
                "ObtainPendingAwaiters_ResumeFirst",
                "ObtainPendingAwaiters_ResumeNext"
            }
        /\  \/  /\  PendingAwaiters # << >>
                /\  UNCHANGED << State, PendingAwaiters >>
            \/  /\  PendingAwaiters = << >>
                /\  State' = [State EXCEPT !.Thread = << >>]
                /\  PendingAwaiters' = State.Thread
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] =
                IF SignallingThreadPCs[thread] = "ObtainPendingAwaiters_ResumeFirst"
                THEN "ResumeFirst"
                ELSE "ResumeNext_Signal"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount >>
        */
        if (m_pendingAwaiters)
        {
            return;
        }

        state_type nextState = state_type{ SignallingState{}, nullptr };
        while (!m_state.compare_exchange_weak(
            lastState,
            nextState,
            std::memory_order_acq_rel,
            std::memory_order_acquire
        ))
        {
            nextState = state_type{ SignallingState{}, lastState.as<SignallingState>() };
        }
        m_pendingAwaiters = lastState.as<SignallingState>();
        lastState = nextState;
    }

public:
    basic_async_auto_reset_event(
        bool isSignalled = false
        )
        :
        m_state{ isSignalled ? state_type{SignalledState{}} : NoWaitingCoroutineState{} }
    {
    }

    bool is_set() const noexcept
    {
        return m_state.load(std::memory_order_acquire) == SignalledState{};
    }

    void set() noexcept
    {
        state_type lastSetState = m_state.load(
            std::memory_order_relaxed
        );
        size_t pendingSignalsToHandleCount = 0;

    signal_start:
        {
            /*
Signal_Start(thread) ==
        /\  SignallingThreadPCs[thread] = "Idle"
        /\  \/  /\  State \in {
                        [ Type |-> "Signalled", Thread |-> << >> ],
                        [ Type |-> "NoWaitingCoroutine", Thread |-> << >> ]
                    }
                /\  State' = [ Type |-> "Signalled", Thread |-> << >> ]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
            \/  /\  State.Type = "Signalling"
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Increment"]
                /\  UNCHANGED << State >>
            \/  /\  State.Type = "WaitingCoroutine"
                /\  State' = [State EXCEPT !.Type = "Signalling" ]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ObtainPendingAwaiters_ResumeFirst"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters  >>
            */
            auto signalStart_state = lastSetState;
            do
            {
                signalStart_state = [&]() -> state_type
                {
                    /*
        /\  \/  /\  State \in {
                        [ Type |-> "Signalled", Thread |-> << >> ],
                        [ Type |-> "NoWaitingCoroutine", Thread |-> << >> ]
                    }
                /\  State' = [ Type |-> "Signalled", Thread |-> << >> ]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                    */
                    if (lastSetState == SignalledState{}
                        ||
                        lastSetState == NoWaitingCoroutineState{})
                    {
                        return SignalledState{};
                    }


                    /*
                                \/  /\  State.Type = "Signalling"
                                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Increment"]
                                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                    */
                    if (lastSetState.is<SignallingState>())
                    {
                        return lastSetState;
                    }

                    /*
                                \/  /\  State.Type = "WaitingCoroutine"
                                    /\  State.Thread # << >>
                                    /\  State' = [State EXCEPT !.Type = "Signalling" ]
                                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_First"]
                                    /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                    */
                    return state_type{ SignallingState{}, lastSetState.as<WaitingCoroutineState>() };
                }();
            } while (!m_state.compare_exchange_weak(
                lastSetState,
                signalStart_state,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            auto signalStart_previousState = lastSetState;
            lastSetState = signalStart_state;

            if (signalStart_previousState == SignalledState{}
                ||
                signalStart_previousState == NoWaitingCoroutineState{})
            {
                return;
            }

            if (signalStart_previousState.is<SignallingState>())
            {
                goto increment;
            }
        }

    resume_first:
        {
            /*
Signal_ResumeFirst(thread) ==
        /\  SignallingThreadPCs[thread] = "ResumeFirst"
        /\  PendingAwaiters' = NextAwaiters[PendingAwaiters[1]]
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![PendingAwaiters[1]] = "Resume"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReadPendingSignals"]
        /\  UNCHANGED << State, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount >>
            */
            obtainPendingAwaiters(
                lastSetState
            );

            auto awaiter_to_resume = m_pendingAwaiters;
            m_pendingAwaiters = m_pendingAwaiters->m_nextAwaiter;
            awaiter_to_resume->m_continuation.resume();
        }

    read_pending_signals:
        {
            /*
Signal_ReadPendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "ReadPendingSignals"
        /\  PendingSignalsToHandleCount' = PendingSignalCount
        /\  PendingSignalCount' = 0
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ResumeNext"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingAwaiters >>
            */
            pendingSignalsToHandleCount = m_pendingSets.exchange(
                0,
                std::memory_order_release
            );
        }
    resume_next:
        {
/*
Signal_ResumeNext(thread) ==
        /\  SignallingThreadPCs[thread] = "ResumeNext"
        /\  \/  /\  PendingSignalsToHandleCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
                /\  UNCHANGED << PendingSignalsToHandleCount >>
            \/  /\  PendingSignalsToHandleCount > 0
                /\  PendingSignalsToHandleCount' = PendingSignalsToHandleCount - 1
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ObtainPendingAwaiters_ResumeNext"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingAwaiters >>
*/
            if (pendingSignalsToHandleCount == 0)
            {
                goto release_signalling_state;
            }
            pendingSignalsToHandleCount--;

            obtainPendingAwaiters(
                lastSetState
            );
            
            /*
Signal_ResumeNext_Signal(thread) ==
        /\  SignallingThreadPCs[thread] = "ResumeNext_Signal"
        /\  \/  /\  PendingAwaiters = << >>
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
                /\  UNCHANGED << ListeningThreadPCs, PendingAwaiters >>
            \/  /\  PendingAwaiters # << >>
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![PendingAwaiters[1]] = "Resume"]
                /\  PendingAwaiters' = NextAwaiters[PendingAwaiters[1]]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ResumeNext"]
        /\  UNCHANGED << State, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount >>
            */
            if (!m_pendingAwaiters)
            {
                goto release_signalling_state;
            }

            auto nextAwaiter = m_pendingAwaiters->m_nextAwaiter;
            m_pendingAwaiters->m_continuation.resume();
            m_pendingAwaiters = nextAwaiter;
            goto resume_next;
        }

    release_signalling_state:
        {
            /*
Signal_ReleaseSignallingState(thread) ==
        /\  SignallingThreadPCs[thread] = "ReleaseSignallingState"
        /\  State' =
                IF  /\  State.Thread = << >>
                    /\  PendingAwaiters = << >>
                THEN [ Type |-> "NoWaitingCoroutine", Thread |-> << >> ]
                ELSE [ Type |-> "WaitingCoroutine", Thread |-> State.Thread ]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
        */
            auto releaseSignallingState_nextState = lastSetState;
            do
            {
                if (lastSetState.as<SignallingState>() == nullptr
                    && !m_pendingAwaiters)
                {
                    releaseSignallingState_nextState = NoWaitingCoroutineState{};
                }
                else
                {
                    releaseSignallingState_nextState = state_type{ WaitingCoroutineState{}, lastSetState.as<SignallingState>() };
                }
            } while (!m_state.compare_exchange_weak(
                lastSetState,
                releaseSignallingState_nextState,
                std::memory_order_release,
                std::memory_order_acquire
            ));
            lastSetState = releaseSignallingState_nextState;

            goto check_for_pending_signals;
        }

    increment:
        {
            /*
            Signal_Increment ==
                \E thread \in SignallingThreads :
                    /\  SignallingThreadPCs[thread] = "Increment"
                    /\  PendingSignalCount' = PendingSignalCount + 1
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters >>
            */
            m_pendingSets.fetch_add(1, std::memory_order_release);
            goto check_for_pending_signals;
        }

    check_for_pending_signals:
        {
            /*
Signal_CheckForPendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "CheckForPendingSignals"
        /\  \/  /\  PendingSignalCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
            \/  /\  PendingSignalCount > 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "HandlePendingSignals"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
                */
            if (m_pendingSets.load(std::memory_order_acquire) == 0)
            {
                return;
            }

            /*
Signal_HandlePendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "HandlePendingSignals"
        /\  \/  /\  State.Type \in { "Signalling", "Signalled", "NoWaitingCoroutine" }
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                /\  UNCHANGED << State >>
            \/  /\  State.Type = "WaitingCoroutine"
                /\  State' = [State EXCEPT !.Type = "Signalling"]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReadPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
            */
            auto handlePendingSignals_nextState = lastSetState;
            do
            {
                if (lastSetState.is<SignallingState>()
                    ||
                    lastSetState.is<SignalledState>()
                    ||
                    lastSetState.is<NoWaitingCoroutineState>())
                {
                    handlePendingSignals_nextState = lastSetState;
                }
                else
                {
                    handlePendingSignals_nextState = state_type{ SignallingState{}, lastSetState.as<WaitingCoroutineState>() };
                }
            } while (!m_state.compare_exchange_weak(
                lastSetState,
                handlePendingSignals_nextState,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            auto handlePendingSignals_previousState = lastSetState;
            lastSetState = handlePendingSignals_nextState;

            if (handlePendingSignals_previousState.is<SignallingState>()
                ||
                handlePendingSignals_previousState.is<SignalledState>()
                ||
                handlePendingSignals_previousState.is<NoWaitingCoroutineState>())
            {
                return;
            }

            goto read_pending_signals;
        }
    }

    void reset() noexcept
    {
        state_type signalled = SignalledState{};

        // If the state is signalled, sets it to no waiting coroutine; there was no waiter, because the state was signalled.
        // If the state is signalling, stays signalling; at the end of signalling, the state will get reset to NoWaitingCoroutineState
        // or WaitingCoroutineState.
        // If the state is WaitingCoroutineState, stays that way.
        m_state.compare_exchange_strong(
            signalled,
            NoWaitingCoroutineState{},
            std::memory_order_release);
    }

    awaiter operator co_await()
    {
        return awaiter{ this };
    }
};

}
using detail::async_auto_reset_event;
}
