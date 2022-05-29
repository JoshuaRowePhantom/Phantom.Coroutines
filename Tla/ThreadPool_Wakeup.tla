----------------------------- MODULE ThreadPool_Wakeup -----------------------------
EXTENDS Sequences, Naturals, Integers, TLC, FiniteSets
CONSTANT Threads, Items

VARIABLE 
    ThreadStates, 
    Queues,
    PendingItems,
    ProcessedItems,
    SleepingThreads,
    IntentsToSleep,
    WakeSignals

vars == <<
    ThreadStates,
    Queues,
    ProcessedItems,
    PendingItems,
    SleepingThreads,
    IntentsToSleep,
    WakeSignals
>>

ThreadStatesType == 
    [Threads ->
        [
            State : 
            { 
                "ProcessingItem", 
                "IntendToSleep_IncrementSleepingThreads", 
                "Wakeup_RemoveIntentToSleep",
                "Sleeping", 
                "Wakeup_DecrementSleepingThreads",
                "Remote"
            }
        ]
        \union
        [
            State : 
            { 
                "Processing", 
                "IntendingToSleep"
            },
            UncheckedQueues : SUBSET Threads
        ]
        \union
        [
            State :
            {
                "Enqueue_CheckSleepingThreads",
                "Enqueue_FindThreadToWake"
            },
            PreviousState : { "Remote", "ProcessingItem" }
        ]
        \union
        [
            State :
            {
                "Enqueue_WakeThread"
            },
            PreviousState : { "Remote", "ProcessingItem" },
            ThreadToWake : Threads
        ]
        \union
        [
            State : { "Wakeup_WakeThreadOtherThanSelf" },
            ThreadToWake : Threads
        ]
    ]

QueuesType ==
    [
        Threads -> 0..Items
    ]

PendingItemsType == 0..Items
ProcessedItemsType == 0..Items
SleepingThreadsType == 0..Cardinality(Threads)
IntentsToSleepType == [Threads -> BOOLEAN]
WakeSignalsType == [Threads -> BOOLEAN]

TypeOk ==
    /\  ThreadStates \in ThreadStatesType
    /\  Queues \in QueuesType
    /\  PendingItems \in PendingItemsType
    /\  ProcessedItems \in ProcessedItemsType
    /\  SleepingThreads \in SleepingThreadsType
    /\  IntentsToSleep \in IntentsToSleepType
    /\  WakeSignals \in WakeSignalsType

\* Choose subsets of threads for each cardinality from 1..Threads-1
\* These sets of threads are used as RemoteThreads.
RemoteThreadsSets ==
    {
        CHOOSE threadSet \in SUBSET Threads :
            Cardinality(threadSet) = count
        :
        count \in 1..Cardinality(Threads)-1
    }

InitialThreadStatesSets ==
    {
        [
            thread \in remoteThreadsSet |-> [
                State |-> "Remote"
            ]
        ]
        @@
        [ 
            thread \in Threads |-> [ 
                    State |-> "Processing",
                    UncheckedQueues |-> Threads
            ]
        ]
        :
        remoteThreadsSet \in RemoteThreadsSets
    }

Init ==
    /\  ThreadStates \in InitialThreadStatesSets
    /\  Queues = [thread \in Threads |-> 0]
    /\  PendingItems = Items
    /\  ProcessedItems = 0
    /\  SleepingThreads = 0
    /\  IntentsToSleep = [thread \in Threads |-> FALSE]
    /\  WakeSignals = [thread \in Threads |-> FALSE]

Enqueue(thread) == 
    LET threadState == ThreadStates[thread] IN
    /\  threadState.State \in { "ProcessingItem", "Remote" }
    /\  PendingItems > 0
    /\  PendingItems' = PendingItems - 1
    /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] + 1]
    /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
            State |-> "Enqueue_CheckSleepingThreads",
            PreviousState |-> threadState.State
        ]]
    /\  UNCHANGED << ProcessedItems, SleepingThreads, IntentsToSleep, WakeSignals >>

Enqueue_CheckSleepingThreads(thread) == 
    LET threadState == ThreadStates[thread] IN
    /\  threadState.State = "Enqueue_CheckSleepingThreads"
    /\  IF SleepingThreads = 0
        THEN
            /\  UNCHANGED << SleepingThreads >>
            /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                    State |-> threadState.PreviousState
                ]]
        ELSE
            /\  SleepingThreads' = SleepingThreads - 1
            /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                    State |-> "Enqueue_FindThreadToWake",
                    PreviousState |-> threadState.PreviousState
                ]]
    /\  UNCHANGED << Queues, PendingItems, ProcessedItems, IntentsToSleep, WakeSignals >>

Enqueue_FindThreadToWake(thread) ==
    LET threadState == ThreadStates[thread] IN
    \E threadToWake \in Threads :
        /\  threadState.State = "Enqueue_FindThreadToWake"
        /\  IntentsToSleep[threadToWake] = TRUE
        /\  IntentsToSleep' = [IntentsToSleep EXCEPT ![threadToWake] = FALSE]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Enqueue_WakeThread",
                PreviousState |-> threadState.PreviousState,
                ThreadToWake |-> threadToWake
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, WakeSignals >>

Enqueue_WakeThread(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Enqueue_WakeThread"
        /\  WakeSignals' = [WakeSignals EXCEPT ![threadState.ThreadToWake] = TRUE]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> threadState.PreviousState
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, IntentsToSleep, SleepingThreads >>

IntendToSleep_MarkIntent(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  Queues[thread] = 0
        /\  threadState.UncheckedQueues = {}
        /\  IF IntentsToSleep[thread] = TRUE
            THEN
                /\  UNCHANGED << IntentsToSleep >>
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "IntendingToSleep",
                        UncheckedQueues |-> Threads
                    ]]
            ELSE
                /\  IntentsToSleep' = [IntentsToSleep EXCEPT ![thread] = TRUE]
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "IntendToSleep_IncrementSleepingThreads"
                    ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, WakeSignals >>

IntendToSleep_IncrementSleepingThreads(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "IntendToSleep_IncrementSleepingThreads"
        /\  SleepingThreads' = SleepingThreads + 1
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "IntendingToSleep",
                UncheckedQueues |-> Threads
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, IntentsToSleep, WakeSignals >>

IntendToSleep_CheckRemoteQueues(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "IntendingToSleep"
        /\  \E otherThread \in threadState.UncheckedQueues :
                IF Queues[otherThread] = 0
                THEN
                    ThreadStates' = [ThreadStates EXCEPT ![thread].UncheckedQueues = threadState.UncheckedQueues \ { otherThread }]
                ELSE
                    ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "Wakeup_DecrementSleepingThreads"
                    ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, IntentsToSleep, SleepingThreads, WakeSignals >>

Sleep(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "IntendingToSleep"
        /\  threadState.UncheckedQueues = {}
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Sleeping"
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep, WakeSignals >>

Wakeup(thread) == 
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Sleeping"
        /\  WakeSignals[thread] = TRUE
        /\  WakeSignals' = [WakeSignals EXCEPT ![thread] = FALSE]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Wakeup_DecrementSleepingThreads"
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep >>

Wakeup_DecrementSleepingThreads(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Wakeup_DecrementSleepingThreads"
        /\  IF SleepingThreads = 0
            THEN
                /\  UNCHANGED << SleepingThreads >>
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "Processing",
                        UncheckedQueues |-> Threads
                    ]]
            ELSE
                /\  SleepingThreads' = SleepingThreads - 1
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "Wakeup_RemoveIntentToSleep"
                    ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, IntentsToSleep, WakeSignals >>

Wakeup_RemoveIntentToSleep(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Wakeup_RemoveIntentToSleep"
        /\  \E sleepingThread \in Threads :
            /\  IntentsToSleep[sleepingThread] = TRUE
            /\  IntentsToSleep' = [IntentsToSleep EXCEPT ![sleepingThread] = FALSE]
            /\  IF sleepingThread # thread 
                THEN 
                    /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                            State |-> "Wakeup_WakeThreadOtherThanSelf",
                            ThreadToWake |-> sleepingThread
                        ]]
                ELSE
                    /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                            State |-> "Processing",
                            UncheckedQueues |-> Threads
                        ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, WakeSignals >>

Wakeup_WakeThreadOtherThanSelf(thread) == 
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Wakeup_WakeThreadOtherThanSelf"
        /\  WakeSignals' = [WakeSignals EXCEPT ![threadState.ThreadToWake] = TRUE]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Processing",
                UncheckedQueues |-> Threads
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep >>

Process(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  Queues[thread] # 0
        /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] - 1]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "ProcessingItem"
            ]]
        /\  UNCHANGED << PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep, WakeSignals >>

TrySteal(thread) ==
    \E sourceThread \in Threads :
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  sourceThread \in threadState.UncheckedQueues
        /\  Queues[thread] = 0
        /\  Queues[sourceThread] = 0
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Processing",
                UncheckedQueues |-> threadState.UncheckedQueues \ { sourceThread }
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep, WakeSignals >>
    
Steal(thread) ==
    \E sourceThread \in Threads :
    \E count \in 1..Queues[sourceThread] :
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  sourceThread \in threadState.UncheckedQueues
        /\  Queues[thread] = 0
        /\  Queues' = [Queues EXCEPT 
                \* Note that a thread that executes a steal
                \* always processes at least one item.
                ![thread] = count - 1,
                ![sourceThread] = Queues[sourceThread] - count
            ]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "ProcessingItem"
            ]]
        /\  UNCHANGED << PendingItems, ProcessedItems, SleepingThreads, IntentsToSleep, WakeSignals >>

ProcessItem(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "ProcessingItem"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Processing",
                UncheckedQueues |-> Threads
            ]]
        /\  ProcessedItems' = ProcessedItems + 1
        /\  UNCHANGED << Queues, PendingItems, SleepingThreads, IntentsToSleep, WakeSignals >>

Complete ==
    /\  ProcessedItems = Items
    /\  \A thread \in Threads: ThreadStates[thread].State \in { "Sleeping", "Remote" }
    /\  UNCHANGED vars

Next ==
    \E thread \in Threads :
        \/  Enqueue(thread)
        \/  Enqueue_CheckSleepingThreads(thread)
        \/  Enqueue_FindThreadToWake(thread)
        \/  Enqueue_WakeThread(thread)
        \* \/  Wakeup(thread)
        \/  Process(thread)
        \/  Steal(thread)
        \/  TrySteal(thread)
        \/  ProcessItem(thread)
        \/  IntendToSleep_IncrementSleepingThreads(thread)
        \/  IntendToSleep_MarkIntent(thread)
        \/  IntendToSleep_CheckRemoteQueues(thread)
        \/  Sleep(thread)
        \/  Wakeup(thread)
        \/  Wakeup_RemoveIntentToSleep(thread)
        \/  Wakeup_DecrementSleepingThreads(thread)
        \/  Wakeup_WakeThreadOtherThanSelf(thread)
        \/  Complete

Spec ==
    /\  Init
    /\  [][Next]_vars

SpecWithFairness ==
    /\  Spec
    /\  \A thread \in Threads :
        /\  WF_vars(Enqueue(thread))
        /\  WF_vars(Enqueue_CheckSleepingThreads(thread))
        /\  WF_vars(Enqueue_FindThreadToWake(thread))
        /\  WF_vars(Enqueue_WakeThread(thread))
        /\  WF_vars(IntendToSleep_CheckRemoteQueues(thread))
        /\  WF_vars(Sleep(thread))
        /\  WF_vars(Wakeup_RemoveIntentToSleep(thread))
        /\  WF_vars(Wakeup_DecrementSleepingThreads(thread))
        /\  WF_vars(Wakeup_WakeThreadOtherThanSelf(thread))
        /\  WF_vars(
                \* Only require fairness of ProcessItem if there is no other useful work to do
                \* We're saying that a given work item can take an arbitrary time to complete,
                \* but that all work items do complete.
                /\  PendingItems = 0
                /\  ProcessItem(thread)
            )
        /\  WF_vars(IntendToSleep_IncrementSleepingThreads(thread))
        /\  WF_vars(IntendToSleep_MarkIntent(thread))
        /\  WF_vars(Wakeup(thread))
        /\  SF_vars(Process(thread))
        /\  SF_vars(Steal(thread))
        /\  SF_vars(TrySteal(thread))

AllItemsGetProcessed ==
    /\  []<>(ProcessedItems = Items)

EnqueueCanAlwaysMakeProgress ==
    [][\A thread \in Threads :
        /\  ThreadStates[thread].State = "Enqueue_CheckSleepingThreads" => ENABLED(Enqueue_CheckSleepingThreads(thread))
        /\  ThreadStates[thread].State = "Enqueue_FindThreadToWake" =>
            \/  ENABLED(Enqueue_FindThreadToWake(thread))
            \/  \E intendingThread \in Threads : 
                \/  ENABLED(IntendToSleep_MarkIntent(intendingThread))
        /\  ThreadStates[thread].State = "Enqueue_WakeThread" => ENABLED(Enqueue_WakeThread(thread))
        /\  (
                /\  ThreadStates[thread].State \in { "Remote", "ProcessingItem" } 
                /\  PendingItems > 0
            ) => ENABLED(Enqueue(thread))
    ]_vars

Alias == [
    ThreadStates |-> ThreadStates,
    Queues |-> Queues,
    PendingItems |-> PendingItems,
    ProcessedItems |-> ProcessedItems,
    SleepingThreads |-> SleepingThreads,
    IntentsToSleep |-> IntentsToSleep,
    WakeSignals |-> WakeSignals,
    EnabledActions |-> [
        thread \in Threads |-> [
            Process |-> ENABLED(Process(thread)),
            Steal |-> ENABLED(Steal(thread)),
            Wakeup |-> ENABLED(Wakeup(thread)),
            Enqueue |-> ENABLED(Enqueue(thread)),
            Enqueue_CheckSleepingThreads |-> ENABLED(Enqueue_CheckSleepingThreads(thread)),
            Enqueue_FindThreadToWake |-> ENABLED(Enqueue_FindThreadToWake(thread)),
            Enqueue_WakeThread |-> ENABLED(Enqueue_WakeThread(thread))
        ]
    ]
]

=============================================================================
