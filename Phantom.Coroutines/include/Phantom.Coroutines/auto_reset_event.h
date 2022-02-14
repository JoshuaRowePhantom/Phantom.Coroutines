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
    // This class follows the algorithm in AutoResetEvent.tla

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
/*
        /\  \/  /\  State.Type = "Signalled"
                /\  State' = [State EXCEPT !.Type = "WaitingCoroutine" ]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Resume"]
                /\  UNCHANGED << NextAwaiters, PendingSignalCount >>
*/
                if (previousState == SignalledState{})
                {
                    return NotSignalledState;
                }

                m_continuation = continuation;

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
/*
    \E thread \in ListeningThreads :
        /\  ListeningThreadPCs[thread] = "Resume"
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Complete"]
        /\  UNCHANGED << SignallingThreadPCs, State, NextAwaiters, PendingSignalCount >>
*/ }
    };

    typedef atomic_state<
        SingletonState<SignalledState>,
        StateSet<SignallingState, awaiter*>,
        StateSet<WaitingCoroutineState, awaiter*>
    > atomic_state_type;
    typedef state<atomic_state_type> state_type;

    static inline const state_type NotSignalledState = state_type{ WaitingCoroutineState{}, nullptr };

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
        state_type lastSetState = m_state.load(
            std::memory_order_relaxed
        );
        size_t pendingSignalCount = m_pendingSets.load(
            std::memory_order_relaxed
        );

    signal_start:
        {
            /*
    Signal_Start ==
        \E thread \in SignallingThreads :
            /\  SignallingThreadPCs[thread] = "Idle"
            /\  \/  /\  State \in {
                            [ Type |-> "Signalled", Thread |-> << >> ],
                            [ Type |-> "WaitingCoroutine", Thread |-> << >> ]
                        }
                    /\  State' = [ Type |-> "Signalled", Thread |-> << >> ]
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                    /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                \/  /\  State.Type = "Signalling"
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Increment"]
                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                \/  /\  State.Type = "WaitingCoroutine"
                    /\  State.Thread # << >>
                    /\  State' = [State EXCEPT !.Type = "Signalling" ]
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_First"]
                    /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
            */
            auto signalStart_previousState = lastSetState;
            auto signalStart_state = lastSetState;
            do
            {
                signalStart_state = [&]() -> state_type
                {
                    /*
                /\  \/  /\  State \in {
                                [ Type |-> "Signalled", Thread |-> << >> ],
                                [ Type |-> "WaitingCoroutine", Thread |-> << >> ]
                            }
                        /\  State' = [ Type |-> "Signalled", Thread |-> << >> ]
                        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                    */
                    if (signalStart_previousState == SignalledState{}
                        ||
                        signalStart_previousState == NotSignalledState)
                    {
                        return SignalledState{};
                    }


                    /*
                                \/  /\  State.Type = "Signalling"
                                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Increment"]
                                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                    */
                    if (signalStart_previousState.is<SignallingState>())
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
                    return state_type{ SignallingState{}, signalStart_previousState.as<WaitingCoroutineState>() };
                }();
            } while (!m_state.compare_exchange_weak(
                signalStart_previousState,
                signalStart_state,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            lastSetState = signalStart_state;

            if (signalStart_previousState == SignalledState{}
                ||
                signalStart_previousState == NotSignalledState)
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
Signal_ResumeFirst ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "Resume_First"
        /\  State' = [State EXCEPT !.Thread = NextAwaiters[State.Thread[1]]]
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![State.Thread[1]] = "Resume"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_Next"]
        /\  UNCHANGED << NextAwaiters, PendingSignalCount >>
                */
            auto resumeFirst_previousState = lastSetState;
            auto resumeFirst_nextState = lastSetState;
            do
            {
                resumeFirst_nextState = state_type{ SignallingState{}, resumeFirst_previousState.as<SignallingState>()->m_nextAwaiter };
            } while (!m_state.compare_exchange_weak(
                resumeFirst_previousState,
                resumeFirst_nextState,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            lastSetState = resumeFirst_nextState;

            auto awaiter_to_resume = resumeFirst_previousState.as<SignallingState>();
            awaiter_to_resume->m_continuation.resume();
        }

    resume_next:
        {
/*
Signal_ResumeNext ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "Resume_Next"
        /\  \/  /\  PendingSignalCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
            \/  /\  PendingSignalCount > 0
                /\  PendingSignalCount' = PendingSignalCount - 1
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ResumeNext_Signal"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters >>
*/
            while (pendingSignalCount != 0)
            {
                if (m_pendingSets.compare_exchange_weak(
                    pendingSignalCount,
                    pendingSignalCount - 1
                ))
                {
                    goto resume_next_signal;
                }
            }
            goto release_signalling_state;
        }


    resume_next_signal:
        {
            /*
            Signal_ResumeNext_Signal ==
                \E thread \in SignallingThreads :
                    /\  SignallingThreadPCs[thread] = "ResumeNext_Signal"
                    /\  \/  /\  State.Thread = << >>
                            /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ResumeNext_EmptyList"]
                            /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                        \/  /\  State.Thread # << >>
                            /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![State.Thread[1]] = "Resume"]
                            /\  State' = [State EXCEPT !.Thread = NextAwaiters[State.Thread[1]]]
                            /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_Next"]
                            /\  UNCHANGED << NextAwaiters, PendingSignalCount >>
            */
            state_type resumeNext_PreviousState = lastSetState;
            state_type resumeNext_NextState = lastSetState;
            do
            {
                if (resumeNext_PreviousState.as<SignallingState>() == nullptr)
                {
                    resumeNext_NextState = lastSetState;
                }
                else
                {
                    resumeNext_NextState = state_type{ SignallingState{}, resumeNext_PreviousState.as<SignallingState>()->m_nextAwaiter };
                }
            } while (!m_state.compare_exchange_weak(
                resumeNext_PreviousState,
                resumeNext_NextState,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            lastSetState = resumeNext_NextState;

            auto awaiterToResume = resumeNext_PreviousState.as<SignallingState>();
            if (!awaiterToResume)
            {
                goto resume_next_empty_list;
            }
            awaiterToResume->m_continuation.resume();
            goto resume_next_signal;
        }

    resume_next_empty_list:
        {
/*
Signal_ResumeNext_EmptyList ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "ResumeNext_EmptyList"
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
        /\  PendingSignalCount' = 0
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters >>
*/
            m_pendingSets.store(
                pendingSignalCount = 0, 
                std::memory_order_release);
            goto release_signalling_state;
        }

    release_signalling_state:
        {
            /*
Signal_ReleaseSignallingState ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "ReleaseSignallingState"
        /\  State' = [State EXCEPT !.Type = "WaitingCoroutine"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
        */
            auto releaseSignallingState_previousState = lastSetState;
            auto releaseSignallingState_nextState = lastSetState;
            do
            {
                releaseSignallingState_nextState = state_type{ WaitingCoroutineState{}, releaseSignallingState_previousState.as<SignallingState>() };
            } while (!m_state.compare_exchange_weak(
                releaseSignallingState_previousState,
                releaseSignallingState_nextState,
                std::memory_order_release,
                std::memory_order_acquire
            ));

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
    Signal_CheckForPendingSignals ==
        \E thread \in SignallingThreads :
            /\  SignallingThreadPCs[thread] = "CheckForPendingSignals"
            /\  \/  /\  PendingSignalCount = 0
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                \/  /\  PendingSignalCount > 0
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "HandlePendingSignals"]
                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                    */
            if (m_pendingSets.load(std::memory_order_acquire) == 0)
            {
                return;
            }

            /*
Signal_HandlePendingSignals ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "HandlePendingSignals"
        /\  \/  /\  State.Type \in { "Signalling", "Signalled" }
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                    /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
                \/  /\  State.Type # "Signalling"
                    /\  State' = [State EXCEPT !.Type = "Signalling"]
                    /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_Next"]
                    /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
            */
            auto handlePendingSignals_previousState = lastSetState;
            auto handlePendingSignals_nextState = lastSetState;
            do
            {
                if (handlePendingSignals_previousState.is<SignallingState>()
                    ||
                    handlePendingSignals_previousState.is<SignalledState>())
                {
                    handlePendingSignals_nextState = handlePendingSignals_previousState;
                }
                else
                {
                    handlePendingSignals_nextState = state_type{ SignallingState{}, handlePendingSignals_previousState.as<WaitingCoroutineState>() };
                }
            } while (!m_state.compare_exchange_weak(
                handlePendingSignals_previousState,
                handlePendingSignals_nextState,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            ));
            lastSetState = handlePendingSignals_nextState;

            if (handlePendingSignals_previousState.is<SignallingState>()
                ||
                handlePendingSignals_previousState.is<SignalledState>())
            {
                return;
            }

            goto resume_next;
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
            NotSignalledState,
            std::memory_order_release);
    }

    awaiter operator co_await()
    {
        return awaiter{ this };
    }
};

}
using detail::auto_reset_event;
}
