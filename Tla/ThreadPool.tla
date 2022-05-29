----------------------------- MODULE ThreadPool -----------------------------
(*
This module describes an algorithm for enqueuing and dequeuing items
in a thread pool. 

Items can be enqueued to a thread when it is either Remote or
Processing another item. Remote threads represent external actors
enqueuing items to the thread pool. During processing of an item,
that item may enqueue items to the current thread.

Each thread maintains state:
* A queue of items, some of which are valid to process
* A head pointer into the queue
  The head pointer is only modified by the thread owning the state
* A tail pointer into the queue
  The tail pointer is modified by other threads executing Steal operations
* A mutex
  The mutex is used to resolve conflicts when a thread dequeues and
  another thread attempts a steal.

*)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Threads, Items

VARIABLE 
    \* The sequence of items not-yet-enqueued
    PendingItems,
    ThreadStates,
    \* A sequence of items that have been enqueued.
    \* Items may be overwritten in the sequence.
    Queues,
    Heads,
    Tails,
    ProcessedItems,
    Locks

vars ==
<<
    PendingItems,
    ThreadStates,
    Queues,
    Heads,
    Tails,
    ProcessedItems,
    Locks
>>

PendingItemsType == Seq(Items)
ThreadStatesType == [Threads ->  
    [
        State : 
        { 
            "Idle",
            "Remote",
            "Process_ReadTail",
            "ProcessInLock",
            "ProcessInLock_ReadTail",
            "ProcessInLock_IncrementHead"
        }
    ]
    \union
    [
        State : {
            "Enqueue_UpdateHead"
        },
        PreviousState : 
        [
            State : { "Remote" }
        ]
        \union
        [
            State : { "Process" },
            Item : Items
        ]
    ]
    \union
    [
        State : { "Steal_ReadSourceThreadTail" },
        SourceThread : Threads
    ]
    \union
    [
        State : { "Steal_ReadSourceThreadHead" },
        SourceThread : Threads,
        SourceThreadTail : Nat
    ]
    \union
    [
        State : { "Steal_Copy" },
        SourceThread : Threads,
        SourceThreadCopyStart : Nat,
        SourceThreadCopyEnd : Nat,
        SourceThreadTail : Nat
    ]
    \union
    [
        State : { "Steal_UpdateTail" },
        SourceThread : Threads,
        SourceThreadTail : Nat,
        SourceThreadHead : Int
    ]
    \union
    [
        State : { "Steal_RereadHead", "Steal_UpdateHead" },
        SourceThread : Threads,
        SourceThreadTail : Nat,
        SourceThreadHead : Int,
        SourceThreadCopyEnd : Nat
    ]
    \union
    [
        State : { "Steal_AdjustTail" },
        SourceThread : Threads,
        SourceThreadTail : Nat,
        SourceThreadHead : Int,
        SourceThreadCopyStart : Nat,
        SourceThreadCopyEnd : Nat
    ]
    \union
    [
        State : { "Process" },
        Item : Items
    ]
]

QueuesType == [Threads -> Seq(Items)]
HeadsType == [Threads -> Int]
TailsType == [Threads -> Nat]
ProcessedItemsType == SUBSET Items
LocksType == [Threads -> BOOLEAN ]

TypeOk ==
    /\  PendingItems \in PendingItemsType
    /\  ThreadStates \in ThreadStatesType
    /\  Queues \in QueuesType
    /\  Heads \in HeadsType
    /\  Tails \in TailsType
    /\  ProcessedItems \in ProcessedItemsType

Lock(thread) ==
    /\  Locks' = [Locks EXCEPT ![thread] = TRUE]
    /\  UNCHANGED << Heads, Tails, Queues, ProcessedItems, PendingItems >>

Unlock(thread) ==
    /\  Locks' = [Locks EXCEPT ![thread] = FALSE]

RECURSIVE SetToSequence(_)
SetToSequence(S) ==
    IF S = {}
    THEN << >>
    ELSE 
        LET s == CHOOSE x \in S : TRUE 
        IN 
        << s >> \o SetToSequence(S \ {s})

GoIdle(thread) ==
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Idle"
            ]]

StartProcessing(thread, item) ==
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Process",
                Item |-> item
            ]]

AddToThreadQueue(thread, item) ==
    /\  Queues' = [Queues EXCEPT ![thread] = Heads[thread] + 1 :> item @@ Queues[thread]]
    /\  UNCHANGED << Heads, Tails, Locks >>

IncrementHead(thread) ==
    /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]
    /\  UNCHANGED << Tails, Locks >>

DecrementHead(thread) ==
    /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] - 1]
    /\  UNCHANGED << Tails, Locks >>

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
                State |-> "Idle"
            ]
        ]
        :
        remoteThreadsSet \in RemoteThreadsSets
    }

Init ==
    /\  PendingItems = SetToSequence(Items)
    /\  ThreadStates \in InitialThreadStatesSets
    /\  Queues = [thread \in Threads |-> << >>]
    /\  Heads = [thread \in Threads |-> 0]
    /\  Tails =  [thread \in Threads |-> 0]
    /\  ProcessedItems = { }
    /\  Locks = [thread \in Threads |-> FALSE]

Enqueue_UpdateQueue(thread) ==
    LET threadState == ThreadStates[thread] IN
    /\  PendingItems # << >>
    /\  threadState.State \in { "Remote", "Process" }
    /\  PendingItems' = Tail(PendingItems)
    /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
            State |-> "Enqueue_UpdateHead",
            PreviousState |-> threadState
        ]]
    /\  AddToThreadQueue(thread, Head(PendingItems))
    /\  UNCHANGED << Heads, Tails, ProcessedItems, Locks >>

Enqueue_UpdateHead(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Enqueue_UpdateHead"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = threadState.PreviousState]
        /\  IncrementHead(thread)
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems, Locks >>

Process_DecrementHead(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Idle"
        /\  DecrementHead(thread)
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Process_ReadTail"
            ]]
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems, Locks >>

Process_ReadTail(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Process_ReadTail"
        /\  IF Tails[thread] > Heads[thread]
            THEN
                \* There is a conflict with a Steal operation.
                \* To resolve the conflict, we acquire the lock
                \* and then continue.
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "ProcessInLock"
                    ]]
            ELSE
                /\  StartProcessing(thread, Queues[thread][Heads[thread] + 1])
        /\  UNCHANGED << PendingItems, Queues, Tails, Heads, ProcessedItems, Locks >>

ProcessInLock(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "ProcessInLock"
        /\  Locks[thread] = FALSE
        /\  Lock(thread)
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "ProcessInLock_ReadTail"
            ]]
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

ProcessInLock_ReadTail(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "ProcessInLock_ReadTail"
        /\  IF Tails[thread] > Heads[thread]
            THEN
                /\  UNCHANGED << Locks >>
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "ProcessInLock_IncrementHead"
                    ]]
            ELSE
                /\  Unlock(thread)
                /\  StartProcessing(thread, Queues[thread][Heads[thread] + 1])
        /\  UNCHANGED << PendingItems, Queues, Tails, Heads, ProcessedItems >>

ProcessInLock_IncrementHead(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "ProcessInLock_IncrementHead"
        /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]
        /\  Unlock(thread)
        /\  GoIdle(thread)
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Steal_Lock(stealingThread) ==
    \E sourceThread \in Threads :
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Idle"
        /\  stealingThread # sourceThread
        /\  Heads[stealingThread] = Tails[stealingThread]
        \* This line isn't implementable, and is just an optimization for state space
        /\  Heads[sourceThread] # Tails[sourceThread]
        /\  Locks[sourceThread] = FALSE
        /\  Lock(sourceThread)
        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                State |-> "Steal_ReadSourceThreadTail",
                SourceThread |-> sourceThread
            ]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems >>

Steal_ReadSourceThreadTail(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_ReadSourceThreadTail"
        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                State |-> "Steal_ReadSourceThreadHead",
                SourceThread |-> threadState.SourceThread,
                SourceThreadTail |-> Tails[threadState.SourceThread]
            ]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems, Locks >>
 
Steal_ReadSourceThreadHead(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_ReadSourceThreadHead"
        /\  /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                    State |-> "Steal_UpdateTail",
                    SourceThread |-> threadState.SourceThread,
                    SourceThreadTail |-> threadState.SourceThreadTail,
                    SourceThreadHead |-> Heads[threadState.SourceThread]
                ]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems, Locks >>

Steal_UpdateTail(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_UpdateTail"
        /\  IF 
                /\  Tails[threadState.SourceThread] = threadState.SourceThreadTail
                /\  \E newTail \in (threadState.SourceThreadTail + 1)..(threadState.SourceThreadHead) : TRUE
            THEN 
                /\  UNCHANGED << Locks >>
                /\  \E newTail \in (threadState.SourceThreadTail + 1)..(threadState.SourceThreadHead) :
                    /\  Tails' = [Tails EXCEPT ![threadState.SourceThread] = newTail]
                    /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                            State |-> "Steal_RereadHead",
                            SourceThread |-> threadState.SourceThread,
                            SourceThreadTail |-> threadState.SourceThreadTail,
                            SourceThreadHead |-> threadState.SourceThreadHead,
                            SourceThreadCopyEnd |-> newTail
                        ]]
            ELSE
                /\  Unlock(threadState.SourceThread)
                /\  GoIdle(stealingThread)
                /\  UNCHANGED << Tails >>
        /\  UNCHANGED << PendingItems, Heads, Queues, ProcessedItems >>

Steal_RereadHead(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_RereadHead"
        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                    State |-> "Steal_AdjustTail",
                    SourceThread |-> threadState.SourceThread,
                    SourceThreadTail |-> threadState.SourceThreadTail,
                    SourceThreadHead |-> Heads[threadState.SourceThread],
                    SourceThreadCopyStart |-> threadState.SourceThreadTail,
                    SourceThreadCopyEnd |-> threadState.SourceThreadCopyEnd
                ]]
        /\  UNCHANGED << PendingItems, Heads, Tails, Queues, ProcessedItems, Locks >>

Steal_AdjustTail(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_AdjustTail"
        /\  IF threadState.SourceThreadHead < threadState.SourceThreadCopyEnd
            THEN
                /\  IF threadState.SourceThreadHead <= threadState.SourceThreadTail
                    THEN
                        /\  Tails' = [Tails EXCEPT ![threadState.SourceThread] = threadState.SourceThreadTail]
                        /\  GoIdle(stealingThread)
                    ELSE
                        /\  Tails' = [Tails EXCEPT ![threadState.SourceThread] = threadState.SourceThreadHead]
                        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                                    State |-> "Steal_Copy",
                                    SourceThread |-> threadState.SourceThread,
                                    SourceThreadTail |-> threadState.SourceThreadTail,
                                    SourceThreadCopyStart |-> threadState.SourceThreadTail,
                                    SourceThreadCopyEnd |-> threadState.SourceThreadHead
                                ]]
            ELSE
                /\  UNCHANGED << Tails >>
                /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                            State |-> "Steal_Copy",
                            SourceThread |-> threadState.SourceThread,
                            SourceThreadTail |-> threadState.SourceThreadTail,
                            SourceThreadCopyStart |-> threadState.SourceThreadTail,
                            SourceThreadCopyEnd |-> threadState.SourceThreadCopyEnd
                        ]]
        /\  Unlock(threadState.SourceThread)
        /\  UNCHANGED << PendingItems, Heads, Queues, ProcessedItems >>

Steal_Copy(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_Copy"
        /\  threadState.SourceThreadCopyStart < threadState.SourceThreadCopyEnd
        /\  Queues' = [Queues EXCEPT ![stealingThread] = 
                (Heads[stealingThread] + threadState.SourceThreadCopyStart - threadState.SourceThreadTail + 1) :> Queues[threadState.SourceThread][threadState.SourceThreadCopyStart + 1]
                @@
                Queues[stealingThread]
            ]
        /\  ThreadStates' = [ThreadStates EXCEPT 
                ![stealingThread].SourceThreadCopyStart =
                    threadState.SourceThreadCopyStart + 1
            ]
        /\  UNCHANGED << PendingItems, Heads, Tails, ProcessedItems, Locks >>

Steal_UpdateHead(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_Copy"
        /\  threadState.SourceThreadCopyStart = threadState.SourceThreadCopyEnd
        /\  Heads' = [Heads EXCEPT ![stealingThread] =
                Heads[stealingThread] + threadState.SourceThreadCopyEnd - threadState.SourceThreadTail - 1
            ]
        /\  StartProcessing(
                stealingThread,
                Queues[stealingThread][Heads[stealingThread] + threadState.SourceThreadCopyEnd - threadState.SourceThreadTail])
        /\  UNCHANGED << PendingItems, Tails, Queues, ProcessedItems, Locks >>

Process(thread) ==
        /\  ThreadStates[thread].State = "Process"
        /\  ProcessedItems' = ProcessedItems \union { ThreadStates[thread].Item }
        /\  GoIdle(thread)
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, Locks >>

IsComplete ==
        /\  PendingItems = << >>
        /\  ProcessedItems = Items

Complete ==
        /\  IsComplete
        /\  UNCHANGED << PendingItems, ThreadStates, Queues, Heads, Tails, ProcessedItems, Locks >>

Next ==
    \E thread \in Threads :
        \/  Enqueue_UpdateQueue(thread)
        \/  Enqueue_UpdateHead(thread)
        \/  Process_DecrementHead(thread)
        \/  Process_ReadTail(thread)
        \/  ProcessInLock(thread)
        \/  ProcessInLock_ReadTail(thread)
        \/  ProcessInLock_IncrementHead(thread)
        \/  Steal_Lock(thread)
        \/  Steal_ReadSourceThreadTail(thread)
        \/  Steal_ReadSourceThreadHead(thread)
        \/  Steal_Copy(thread)
        \/  Steal_UpdateTail(thread)
        \/  Steal_RereadHead(thread)
        \/  Steal_AdjustTail(thread)
        \/  Steal_UpdateHead(thread)
        \/  Process(thread)
        \/  Complete

Spec ==
    /\  Init
    /\  [][Next]_vars

SpecWithFairness ==
    /\  Spec
    /\  \A thread \in Threads :
        /\  SF_vars(Enqueue_UpdateQueue(thread))
        /\  WF_vars(Enqueue_UpdateHead(thread))
        /\  WF_vars(Process_DecrementHead(thread))
        /\  WF_vars(Process_ReadTail(thread))
        /\  WF_vars(ProcessInLock(thread))
        /\  WF_vars(ProcessInLock_ReadTail(thread))
        /\  WF_vars(ProcessInLock_IncrementHead(thread))
        /\  WF_vars(Steal_ReadSourceThreadTail(thread))
        /\  WF_vars(Steal_ReadSourceThreadHead(thread))
        /\  WF_vars(Steal_Copy(thread))
        /\  WF_vars(Steal_UpdateTail(thread))
        /\  WF_vars(Steal_RereadHead(thread))
        /\  WF_vars(Steal_AdjustTail(thread))
        /\  WF_vars(Steal_Copy(thread))
        /\  WF_vars(Steal_UpdateHead(thread))
        /\  WF_vars(Process(thread))

AllItemsGetProcessed ==
    []<>(IsComplete)

NoItemIsProcessedInDuplicate ==
    [][(\E thread \in Threads : Process(thread)) => ProcessedItems # ProcessedItems']_vars

Alias ==
    [
        Heads |-> Heads,
        Tails |-> Tails,
        PendingItems |-> PendingItems,
        ProcessedItems |-> ProcessedItems,
        Queues |-> Queues,
        ThreadStates |-> ThreadStates,
        EnabledActions |-> [
            thread \in Threads |-> [
                Enqueue_UpdateHead |-> ENABLED(Enqueue_UpdateHead(thread))
            ]
        ]
    ]       

Symmetry == Permutations(Threads) \union Permutations(Items)
  
=============================================================================
