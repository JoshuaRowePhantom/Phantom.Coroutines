----------------------------- MODULE ThreadPool -----------------------------

EXTENDS Integers, Sequences, FiniteSets

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

PendingItemsType == SUBSET Items
ThreadStatesType == [Threads ->  
    [
        State : { "Idle", "Enqueue_UpdateHead" }
    ]
    \union
    [
        State : { "Process_CompareTailToHead" },
        Tail : Nat
    ]
    \union
    [
        State : { "Steal_IncrementSourceThreadTail" },
        SourceThreadHead : Nat,
        SourceThread : Threads
    ]
    \union
    [
        State : { "Steal_ProcessFirst" },
        Item : Items
    ]
]

QueuesType == [Threads -> Seq(Items)]
HeadsType == [Threads -> Nat]
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

Init ==
    /\  PendingItems = Items
    /\  ThreadStates = [thread \in Threads |-> [State |-> "Idle"]]
    /\  Queues = [thread \in Threads |-> << >>]
    /\  Heads = [thread \in Threads |-> 0]
    /\  Tails =  [thread \in Threads |-> 0]
    /\  ProcessedItems = << >>

Enqueue_UpdateQueue(thread) ==
    \E item \in PendingItems :
        /\  ThreadStates[thread].State = "Idle"
        /\  PendingItems' = PendingItems \ { item }
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Enqueue_UpdateHead"
            ]]
        /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] \o << item >>]
        /\  UNCHANGED << Heads, Tails, ProcessedItems >>

Enqueue_UpdateHead(thread) ==
        /\  ThreadStates[thread].State = "Enqueue_UpdateHead"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [State |-> "Idle"]]
        /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Process(thread) ==
        /\  ThreadStates[thread].State = "Idle"
        /\  Tails[thread] < Heads[thread]
        /\  Tails' = [Tails EXCEPT ![thread] = Tails[thread] + 1]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Idle"
            ]]
        /\  ProcessedItems' = ProcessedItems \o << Queues[thread][Tails[thread] + 1] >>
        /\  UNCHANGED << PendingItems, Queues, Heads >>

Steal_ReadSourceThreadHead(stealingThread) ==
    \E sourceThread \in Threads :
    \E newTail \in (Tails[sourceThread] + 1)..(Heads[sourceThread]) :
        /\  ThreadStates[stealingThread].State = "Idle"
        /\  stealingThread # sourceThread
        /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                State |-> "Steal_IncrementSourceThreadTail",
                SourceThread |-> sourceThread,
                SourceThreadHead |-> Heads[sourceThread]]]
        /\  UNCHANGED << PendingItems, Queues, Heads, Tails, ProcessedItems >>
  
Steal_IncrementSourceThreadTail(stealingThread) ==
        /\  ThreadStates[stealingThread].State = "Steal_IncrementSourceThreadTail"
        /\  LET sourceThread == ThreadStates[stealingThread].SourceThread
                sourceThreadTail == Tails[sourceThread]
                sourceThreadHead == ThreadStates[stealingThread].SourceThreadHead 
            IN
            IF sourceThreadTail >= sourceThreadHead
            THEN
                /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [ State |-> "Idle" ]]
                /\  UNCHANGED << Queues, Tails >>
            ELSE
                \E newTail \in (sourceThreadTail + 1)..(sourceThreadHead) :
                    /\  Tails' = [Tails EXCEPT ![sourceThread] = newTail]
                    /\  Queues' = [Queues EXCEPT ![stealingThread] = Queues[stealingThread] \o SubSeq(Queues[sourceThread], sourceThreadTail + 2, newTail)]
                    /\  ThreadStates' = [ThreadStates EXCEPT ![stealingThread] = [
                            State |-> "Steal_ProcessFirst",
                            Item |-> Queues[sourceThread][sourceThreadTail + 1]
                        ]]
        /\  UNCHANGED << PendingItems, Heads, ProcessedItems >>

Steal_ProcessFirst(thread) ==
        /\  ThreadStates[thread].State = "Steal_ProcessFirst"
        /\  Heads' = [Heads EXCEPT ![thread] = Len(Queues[thread])]
        /\  ProcessedItems' = ProcessedItems \o << ThreadStates[thread].Item >>
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [ State |-> "Idle"]]
        /\  UNCHANGED << PendingItems, Queues, Tails >>

Next ==
    \E thread \in Threads :
        \/  Enqueue_UpdateQueue(thread)
        \/  Enqueue_UpdateHead(thread)
        \/  Process(thread)
        \/  Steal_ReadSourceThreadHead(thread)
        \/  Steal_IncrementSourceThreadTail(thread)
        \/  Steal_ProcessFirst(thread)

Spec ==
    /\  Init
    /\  [][Next]_vars

SpecWithFairness ==
    /\  Spec
    /\  \A thread \in Threads :
        /\  WF_vars(Process(thread))
        /\  WF_vars(Steal_IncrementSourceThreadTail(thread))
        /\  WF_vars(Steal_ProcessFirst(thread))
        /\  WF_vars(Enqueue_UpdateHead(thread))
        /\  WF_vars(Enqueue_UpdateQueue(thread))

AllItemsGetProcessed ==
    []<>(ProcessedItemsSet = Items)

NoItemIsProcessedInDuplicate ==
    Cardinality(DOMAIN(ProcessedItems)) = Cardinality(ProcessedItemsSet)
         
=============================================================================
