--------------------------- MODULE AutoResetEvent ---------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT SignallingThreads, ListeningThreads

VARIABLE
    SignallingThreadPCs,
    ListeningThreadPCs,
    State,
    NextAwaiters,
    PendingSignalCount

vars == <<
    SignallingThreadPCs,
    ListeningThreadPCs,
    State,
    NextAwaiters,
    PendingSignalCount
>>

ListeningThreadList == [ { 1 } -> ListeningThreads ] \union {<< >>}
 
StateType ==  
    [   Type : { "Signalled",
                 "Signalling",
                 "WaitingCoroutine" },
        Thread : ListeningThreadList  
    ]


SignallingThreadPCsType == [ SignallingThreads -> {
    "Idle",
    "Complete",
    "Increment",
    "ReleaseSignallingState",
    "CheckForPendingSignals",
    "HandlePendingSignals",
    "Resume_First",
    "Resume_Next",
    "ResumeNext_EmptyList",
    "ResumeNext_EmptyList_SignalAllWaiters",
    "ResumeNext_Signal"
}]

ListeningThreadPCsType == [ ListeningThreads -> {
    "Idle",
    "Pending",
    "Resume",
    "Complete"
}]

NextAwaitersType == [ ListeningThreads -> ListeningThreadList ]

PendingSignalCountType == Nat

TypeOk ==
    /\  SignallingThreadPCs \in SignallingThreadPCsType 
    /\  ListeningThreadPCs \in ListeningThreadPCsType 
    /\  State \in StateType
    /\  NextAwaiters \in NextAwaitersType
    /\  PendingSignalCount \in PendingSignalCountType

Init ==
    /\  SignallingThreadPCs = [ threads \in SignallingThreads |-> "Idle" ]
    /\  ListeningThreadPCs = [ threads \in ListeningThreads |-> "Idle" ]
    /\  State = [ Type |-> "WaitingCoroutine", Thread |-> << >> ]
    /\  NextAwaiters = [ thread \in ListeningThreads |-> << >> ]
    /\  PendingSignalCount = 0

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

Signal_ResumeFirst ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "Resume_First"
        /\  State' = [State EXCEPT !.Thread = NextAwaiters[State.Thread[1]]]
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![State.Thread[1]] = "Resume"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Resume_Next"]
        /\  UNCHANGED << NextAwaiters, PendingSignalCount >>

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

Signal_ResumeNext_EmptyList ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "ResumeNext_EmptyList"
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
        /\  PendingSignalCount' = 0
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters >>

Signal_Increment ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "Increment"
        /\  PendingSignalCount' = PendingSignalCount + 1
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters >>

Signal_ReleaseSignallingState ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "ReleaseSignallingState"
        /\  State' = [State EXCEPT !.Type = "WaitingCoroutine"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount >>

Signal_CheckForPendingSignals ==
    \E thread \in SignallingThreads :
        /\  SignallingThreadPCs[thread] = "CheckForPendingSignals"
        /\  \/  /\  PendingSignalCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>
            \/  /\  PendingSignalCount > 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "HandlePendingSignals"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount >>

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

Listen_Start ==
    \E  thread \in ListeningThreads :
        /\  ListeningThreadPCs[thread] = "Idle"
        /\  \/  /\  State.Type = "Signalled"
                /\  State' = [State EXCEPT !.Type = "WaitingCoroutine" ]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Resume"]
                /\  UNCHANGED << NextAwaiters, PendingSignalCount >>
            \/  /\  State.Type \in { "WaitingCoroutine", "Signalling" }
                /\  State' = [State EXCEPT !.Thread = << thread >> ]
                /\  NextAwaiters' = [NextAwaiters EXCEPT ![thread] = State.Thread]
                /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Pending"]
                /\  UNCHANGED << PendingSignalCount >>
        /\  UNCHANGED << SignallingThreadPCs >>

Listen_Resume ==
    \E thread \in ListeningThreads :
        /\  ListeningThreadPCs[thread] = "Resume"
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![thread] = "Complete"]
        /\  UNCHANGED << SignallingThreadPCs, State, NextAwaiters, PendingSignalCount >>

Next ==
    \/  Signal_Start
    \/  Signal_ResumeFirst
    \/  Signal_ResumeNext
    \/  Signal_ResumeNext_Signal
    \/  Signal_ResumeNext_EmptyList
    \/  Signal_ReleaseSignallingState
    \/  Signal_CheckForPendingSignals
    \/  Signal_HandlePendingSignals
    \/  Signal_Increment
    \/  Listen_Start
    \/  Listen_Resume

CardinalityOfSignallingThreads(state) == Cardinality({ thread \in SignallingThreads : SignallingThreadPCs[thread] = state })
CardinalityOfListeningThreads(state) == Cardinality({ thread \in ListeningThreads : ListeningThreadPCs[thread] = state })

NoMoreSignalledThreadsThanSignals == Cardinality({ thread \in SignallingThreads : SignallingThreadPCs[thread] # "Idle" }) >= CardinalityOfListeningThreads("Complete")

AllPendingThreadsGetSignalled ==[](
    \A pendingThreadCount \in 1..Cardinality(ListeningThreads) :
    \A alreadyCompletedThreadCount \in 1..Cardinality(ListeningThreads) :
    ( 
        /\  CardinalityOfListeningThreads("Pending") = pendingThreadCount
        /\  CardinalityOfListeningThreads("Completed") = alreadyCompletedThreadCount
        /\  CardinalityOfSignallingThreads("Idle") >= pendingThreadCount
    ) ~> CardinalityOfListeningThreads("Complete") >= pendingThreadCount + alreadyCompletedThreadCount)

PermittedListeningThreadStateChanges == [][
    \A thread \in ListeningThreads :
        << ListeningThreadPCs[thread], ListeningThreadPCs'[thread] >> \in {
            << "Idle", "Idle" >>,
            << "Idle", "Pending" >>,
            << "Pending", "Pending" >>,
            << "Idle", "Resume" >>,
            << "Pending", "Resume" >>,
            << "Resume", "Resume" >>,
            << "Resume", "Complete" >>,
            << "Complete", "Complete" >>
        }
    ]_ListeningThreadPCs
    
ForwardProgressCanBeMadeBySignallingThreads == 
    /\
        \/  \A  thread \in SignallingThreads :
            SignallingThreadPCs[thread] = "Complete"
        \/  ENABLED(Signal_Start)
        \/  ENABLED(Signal_Increment)
        \/  ENABLED(Signal_ResumeFirst)
        \/  ENABLED(Signal_ResumeNext)
        \/  ENABLED(Signal_ResumeNext_Signal)
        \/  ENABLED(Signal_ResumeNext_EmptyList)
        \/  ENABLED(Signal_ReleaseSignallingState)
        \/  ENABLED(Signal_CheckForPendingSignals)
        \/  ENABLED(Signal_HandlePendingSignals)

ForwardProgressCanBeMadeByListeningThreads ==
    /\
        \/  \A  thread \in ListeningThreads :
            ListeningThreadPCs[thread] \in { "Pending", "Complete" }
        \/  ENABLED(Listen_Start)
        \/  ENABLED(Listen_Resume)

ForwardProgressCanBeMade ==
    /\  ForwardProgressCanBeMadeBySignallingThreads
    /\  ForwardProgressCanBeMadeByListeningThreads
    
Invariant ==
    /\  TypeOk
    /\  NoMoreSignalledThreadsThanSignals 
    /\  ForwardProgressCanBeMade

Spec ==
    /\  Init
    /\  [][Next]_vars

Fairness ==
    /\  SF_vars(Next)

SpecWithFairness ==
    /\  Spec
    /\  Fairness

DebugEnabled == [
    Next |-> ENABLED(Next),
    Signal_Start |-> ENABLED(Signal_Start),
    Listen_Start |-> ENABLED(Listen_Start)
]

=============================================================================
