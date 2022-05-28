----------------------------- MODULE ThreadPool -----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Threads, Items

VARIABLE 
    PendingItems,
    ThreadStates,
    Queues,
    Heads,
    Tails,
    ProcessedItems

vars ==
<<
    PendingItems,
    ThreadStates,
    Queues,
    Heads,
    Tails,
    ProcessedItems
>>

PendingItemsType == Seq(Items)
ThreadStatesType == [Threads ->  
    [
        State : { "Idle", "Enqueue_UpdateHead", "Process_IncrementHead", "Process_ReadTail" }
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
ProcessedItemsType == Seq(Items)

TypeOk ==
    /\  PendingItems \in PendingItemsType
    /\  ThreadStates \in ThreadStatesType
    /\  Queues \in QueuesType
    /\  Heads \in HeadsType
    /\  Tails \in TailsType
    /\  ProcessedItems \in ProcessedItemsType

ProcessedItemsSet == { ProcessedItems[index] : index \in DOMAIN(ProcessedItems)}

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

IncrementHead(thread) ==
    /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]

DecrementHead(thread) ==
    /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] - 1]

Init ==
    /\  PendingItems = SetToSequence(Items)
    /\  ThreadStates = [thread \in Threads |-> [State |-> "Idle"]]
    /\  Queues = [thread \in Threads |-> << >>]
    /\  Heads = [thread \in Threads |-> 0]
    /\  Tails =  [thread \in Threads |-> 0]
    /\  ProcessedItems = << >>

Enqueue_UpdateQueue(thread) ==
    /\  PendingItems # << >>
    /\  ThreadStates[thread].State = "Idle"
    /\  PendingItems' = Tail(PendingItems)
    /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
            State |-> "Enqueue_UpdateHead"
        ]]
    /\  AddToThreadQueue(thread, Head(PendingItems))
    /\  UNCHANGED << Heads, Tails, ProcessedItems >>

Enqueue_UpdateHead(thread) ==
        /\  ThreadStates[thread].State = "Enqueue_UpdateHead"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [State |-> "Idle"]]
        /\  IncrementHead(thread)
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Process_DecrementHead(thread) ==
        /\  ThreadStates[thread].State = "Idle"
        /\  DecrementHead(thread)
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Process_ReadTail"
            ]]
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Process_ReadTail(thread) ==
        /\  ThreadStates[thread].State = "Process_ReadTail"
        /\  IF Tails[thread] > Heads[thread]
            THEN
                /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                        State |-> "Process_IncrementHead"
                    ]]
            ELSE
                /\  StartProcessing(thread, Queues[thread][Heads[thread] + 1])
        /\  UNCHANGED << PendingItems, Queues, Tails, Heads, ProcessedItems >>
        
Process_IncrementHead(thread) ==
        /\  ThreadStates[thread].State = "Process_IncrementHead"
        /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]
        /\  GoIdle(thread)
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Steal_ReadSourceThreadTail(stealingThread) ==
    \E sourceThread \in Threads :
    LET threadState == ThreadStates[stealingThread] IN
        /\  stealingThread # sourceThread
        /\  Heads[stealingThread] = Tails[stealingThread]
        /\  threadState.State = "Idle"
        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                State |-> "Steal_ReadSourceThreadHead",
                SourceThread |-> sourceThread,
                SourceThreadTail |-> Tails[sourceThread]
            ]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems >>
 
Steal_ReadSourceThreadHead(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_ReadSourceThreadHead"
        /\  /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                    State |-> "Steal_UpdateTail",
                    SourceThread |-> threadState.SourceThread,
                    SourceThreadTail |-> threadState.SourceThreadTail,
                    SourceThreadHead |-> Heads[threadState.SourceThread]
                ]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems >>

Steal_UpdateTail(stealingThread) ==
    LET threadState == ThreadStates[stealingThread] IN
        /\  threadState.State = "Steal_UpdateTail"
        /\  IF 
                /\  Tails[threadState.SourceThread] = threadState.SourceThreadTail
                /\  \E newTail \in (threadState.SourceThreadTail + 1)..(threadState.SourceThreadHead) : TRUE
            THEN 
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
        /\  UNCHANGED << PendingItems, Heads, Tails, Queues, ProcessedItems >>

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
        /\  UNCHANGED << PendingItems, Heads, Tails, ProcessedItems >>

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
        /\  UNCHANGED << PendingItems, Tails, Queues, ProcessedItems >>

Process(thread) ==
        /\  ThreadStates[thread].State = "Process"
        /\  ProcessedItems' = ProcessedItems \o << ThreadStates[thread].Item >>
        /\  GoIdle(thread)
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails >>

IsComplete ==
        /\  PendingItems = << >>
        /\  ProcessedItemsSet = Items

Complete ==
        /\  IsComplete
        /\  UNCHANGED << PendingItems, ThreadStates, Queues, Heads, Tails, ProcessedItems >>

Next ==
    \E thread \in Threads :
        \/  Enqueue_UpdateQueue(thread)
        \/  Enqueue_UpdateHead(thread)
        \/  Process_DecrementHead(thread)
        \/  Process_ReadTail(thread)
        \/  Process_IncrementHead(thread)
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
        /\  WF_vars(Process_IncrementHead(thread))
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
    Cardinality(DOMAIN(ProcessedItems)) = Cardinality(ProcessedItemsSet)

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
