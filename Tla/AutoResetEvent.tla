--------------------------- MODULE AutoResetEvent ---------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT SignallingThreads, ListeningThreads

VARIABLE
    SignallingThreadPCs,
    ListeningThreadPCs,
    State,
    NextAwaiters,
    PendingSignalCount,
    PendingSignalsToHandleCount,
    PendingAwaiters

vars == <<
    SignallingThreadPCs,
    ListeningThreadPCs,
    State,
    NextAwaiters,
    PendingSignalCount,
    PendingSignalsToHandleCount,
    PendingAwaiters
>>

ListeningThreadList == [ { 1 } -> ListeningThreads ] \union {<< >>}
 
StateType ==  
    [   Type : { "Signalled",
                 "Signalling",
                 "NoWaitingCoroutine",
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
    "ResumeFirst",
    "ReadPendingSignals",
    "ResumeNext",
    "ResumeNext_Signal",
    "ObtainPendingAwaiters_ResumeFirst",
    "ObtainPendingAwaiters_ResumeNext"
}]

ListeningThreadPCsType == [ ListeningThreads -> {
    "Idle",
    "Pending",
    "Resume"
}]

NextAwaitersType == [ ListeningThreads -> ListeningThreadList ]

PendingSignalCountType == Nat
PendingSignalsToHandleCountType == Nat
PendingAwaitersType == ListeningThreadList

TypeOk ==
    /\  SignallingThreadPCs \in SignallingThreadPCsType 
    /\  ListeningThreadPCs \in ListeningThreadPCsType 
    /\  State \in StateType
    /\  NextAwaiters \in NextAwaitersType
    /\  PendingSignalCount \in PendingSignalCountType
    /\  PendingSignalsToHandleCount \in PendingSignalsToHandleCountType
    /\  PendingAwaiters \in PendingAwaitersType

Init ==
    /\  SignallingThreadPCs = [ threads \in SignallingThreads |-> "Idle" ]
    /\  ListeningThreadPCs = [ threads \in ListeningThreads |-> "Idle" ]
    /\  State = [ Type |-> "NoWaitingCoroutine", Thread |-> << >> ]
    /\  NextAwaiters = [ thread \in ListeningThreads |-> << >> ]
    /\  PendingSignalCount = 0
    /\  PendingSignalsToHandleCount = 0
    /\  PendingAwaiters = << >>

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

Signal_ResumeFirst(thread) ==
        /\  SignallingThreadPCs[thread] = "ResumeFirst"
        /\  PendingAwaiters' = NextAwaiters[PendingAwaiters[1]]
        /\  ListeningThreadPCs' = [ListeningThreadPCs EXCEPT ![PendingAwaiters[1]] = "Resume"]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReadPendingSignals"]
        /\  UNCHANGED << State, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount >>

Signal_ReadPendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "ReadPendingSignals"
        /\  PendingSignalsToHandleCount' = PendingSignalCount
        /\  PendingSignalCount' = 0
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ResumeNext"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingAwaiters >>

Signal_ResumeNext(thread) ==
        /\  SignallingThreadPCs[thread] = "ResumeNext"
        /\  \/  /\  PendingSignalsToHandleCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReleaseSignallingState"]
                /\  UNCHANGED << PendingSignalsToHandleCount >>
            \/  /\  PendingSignalsToHandleCount > 0
                /\  PendingSignalsToHandleCount' = PendingSignalsToHandleCount - 1
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ObtainPendingAwaiters_ResumeNext"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingAwaiters >>
        
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

Signal_Increment(thread) ==
        /\  SignallingThreadPCs[thread] = "Increment"
        /\  PendingSignalCount' = PendingSignalCount + 1
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalsToHandleCount, PendingAwaiters >>

Signal_ReleaseSignallingState(thread) ==
        /\  SignallingThreadPCs[thread] = "ReleaseSignallingState"
        /\  State' =
                IF  /\  State.Thread = << >>
                    /\  PendingAwaiters = << >>
                THEN [ Type |-> "NoWaitingCoroutine", Thread |-> << >> ]
                ELSE [ Type |-> "WaitingCoroutine", Thread |-> State.Thread ]
        /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "CheckForPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>

Signal_CheckForPendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "CheckForPendingSignals"
        /\  \/  /\  PendingSignalCount = 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>
            \/  /\  PendingSignalCount > 0
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "HandlePendingSignals"]
                /\  UNCHANGED << State, ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>

Signal_HandlePendingSignals(thread) ==
        /\  SignallingThreadPCs[thread] = "HandlePendingSignals"
        /\  \/  /\  State.Type \in { "Signalling", "Signalled", "NoWaitingCoroutine" }
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "Complete"]
                /\  UNCHANGED << State >>
            \/  /\  State.Type = "WaitingCoroutine"
                /\  State' = [State EXCEPT !.Type = "Signalling"]
                /\  SignallingThreadPCs' = [SignallingThreadPCs EXCEPT ![thread] = "ReadPendingSignals"]
        /\  UNCHANGED << ListeningThreadPCs, NextAwaiters, PendingSignalCount, PendingSignalsToHandleCount, PendingAwaiters >>

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

Next ==
    \/  \E thread \in SignallingThreads :
        \/  Signal_Start(thread)
        \/  Signal_ResumeFirst(thread)
        \/  Signal_ReadPendingSignals(thread)
        \/  Signal_ResumeNext(thread)
        \/  Signal_ResumeNext_Signal(thread)
        \/  Signal_ReleaseSignallingState(thread)
        \/  Signal_CheckForPendingSignals(thread)
        \/  Signal_HandlePendingSignals(thread)
        \/  Signal_Increment(thread)
        \/  Signal_ObtainPendingAwaiters(thread)
    \/  \E  thread \in ListeningThreads :
        \/  Listen_Start(thread)

CardinalityOfSignallingThreads(state) == Cardinality({ thread \in SignallingThreads : SignallingThreadPCs[thread] = state })
CardinalityOfListeningThreads(state) == Cardinality({ thread \in ListeningThreads : ListeningThreadPCs[thread] = state })

NoMoreSignalledThreadsThanSignals == Cardinality({ thread \in SignallingThreads : SignallingThreadPCs[thread] # "Idle" }) >= CardinalityOfListeningThreads("Resume")

AllPendingThreadsGetSignalled ==[](
    \A pendingThreadCount \in 1..Cardinality(ListeningThreads) :
    \A alreadyCompletedThreadCount \in 1..Cardinality(ListeningThreads) :
    ( 
        /\  CardinalityOfListeningThreads("Pending") = pendingThreadCount
        /\  CardinalityOfListeningThreads("Resume") = alreadyCompletedThreadCount
        /\  CardinalityOfSignallingThreads("Idle") >= pendingThreadCount
    ) ~> CardinalityOfListeningThreads("Resume") >= pendingThreadCount + alreadyCompletedThreadCount)

PermittedListeningThreadStateChanges == [][
    \A thread \in ListeningThreads :
        << ListeningThreadPCs[thread], ListeningThreadPCs'[thread] >> \in {
            << "Idle", "Idle" >>,
            << "Idle", "Pending" >>,
            << "Pending", "Pending" >>,
            << "Idle", "Resume" >>,
            << "Pending", "Resume" >>,
            << "Resume", "Resume" >>
        }
    ]_ListeningThreadPCs
    
ForwardProgressCanBeMadeBySignallingThreads == 
    /\
        \/  \A  thread \in SignallingThreads :
            \/  SignallingThreadPCs[thread] = "Complete"
            \/  ENABLED(Signal_Start(thread))
            \/  ENABLED(Signal_Increment(thread))
            \/  ENABLED(Signal_ResumeFirst(thread))
            \/  ENABLED(Signal_ReadPendingSignals(thread))
            \/  ENABLED(Signal_ResumeNext(thread))
            \/  ENABLED(Signal_ResumeNext_Signal(thread))
            \/  ENABLED(Signal_ReleaseSignallingState(thread))
            \/  ENABLED(Signal_CheckForPendingSignals(thread))
            \/  ENABLED(Signal_HandlePendingSignals(thread))
            \/  ENABLED(Signal_ObtainPendingAwaiters(thread))

ForwardProgressCanBeMadeByListeningThreads ==
    /\
        \/  \A  thread \in ListeningThreads :
            ListeningThreadPCs[thread] = "Idle" => ENABLED(Listen_Start(thread))

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
    SignallingThreads |-> [ thread \in SignallingThreads |-> [
        Signal_Start |-> ENABLED(Signal_Start(thread)),                  
        Signal_Increment |-> ENABLED(Signal_Increment(thread)),              
        Signal_ResumeFirst |-> ENABLED(Signal_ResumeFirst(thread)),
        Signal_ReadPendingSignals |-> ENABLED(Signal_ReadPendingSignals(thread)),
        Signal_ResumeNext |-> ENABLED(Signal_ResumeNext(thread)),          
        Signal_ResumeNext_Signal |-> ENABLED(Signal_ResumeNext_Signal(thread)),      
        Signal_ReleaseSignallingState |-> ENABLED(Signal_ReleaseSignallingState(thread)), 
        Signal_CheckForPendingSignals |-> ENABLED(Signal_CheckForPendingSignals(thread)), 
        Signal_HandlePendingSignals |-> ENABLED(Signal_HandlePendingSignals(thread)),   
        Signal_ObtainPendingAwaiters |-> ENABLED(Signal_ObtainPendingAwaiters(thread))  
    ]],
    ListeningThreads |-> [ thread \in ListeningThreads |-> [
        Listen_State |-> ENABLED(Listen_Start(thread)) ]]
]

=============================================================================
