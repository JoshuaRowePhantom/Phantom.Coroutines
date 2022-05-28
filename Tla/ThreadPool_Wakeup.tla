----------------------------- MODULE ThreadPool_Wakeup -----------------------------
EXTENDS Sequences, Naturals, Integers
CONSTANT Threads, Items

VARIABLE 
    ThreadStates, 
    Queues,
    PendingItems,
    ProcessedItems

vars == <<
    ThreadStates,
    Queues,
    ProcessedItems,
    PendingItems
>>

ThreadStatesType == 
    [Threads ->
        [
            State : { "Sleeping", "Processing", "ProcessingItem" }
        ]
    ]

QueuesType ==
    [
        Threads -> Nat
    ]

PendingItemsType == Nat
ProcessedItemsType == Nat

TypeOk ==
    /\  ThreadStates \in ThreadStatesType
    /\  Queues \in QueuesType
    /\  PendingItems \in PendingItemsType
    /\  ProcessedItems \in ProcessedItemsType

Init ==
    /\  ThreadStates = [thread \in Threads |-> [ State |-> "Processing"]]
    /\  Queues = [thread \in Threads |-> 0]
    /\  PendingItems = Items
    /\  ProcessedItems = 0

Enqueue(thread) == 
    /\  PendingItems > 0
    /\  PendingItems' = PendingItems - 1
    /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] + 1]
    /\  UNCHANGED << ThreadStates, ProcessedItems >>

Wakeup(thread) == 
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Sleeping"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Processing"
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems >>

Sleep(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Sleeping"
            ]]
        /\  UNCHANGED << Queues, PendingItems, ProcessedItems >>

Process(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  Queues[thread] # 0
        /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] - 1]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "ProcessingItem"
            ]]
        /\  UNCHANGED << PendingItems, ProcessedItems >>

Steal(thread) ==
    \E sourceThread \in Threads :
    \E count \in 1..Queues[sourceThread] :
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "Processing"
        /\  Queues[sourceThread] = 0
        /\  Queues' = [Queues EXCEPT 
                \* Note that a thread that executes a steal
                \* always processes at least one item.
                ![thread] = count - 1,
                ![sourceThread] = Queues[sourceThread] - count
            ]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "ProcessingItem"
            ]]
        /\  UNCHANGED << ThreadStates, PendingItems, ProcessedItems >>

ProcessItem(thread) ==
    LET threadState == ThreadStates[thread] IN
        /\  threadState.State = "ProcessingItem"
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = [
                State |-> "Processing"
            ]]
        /\  ProcessedItems' = ProcessedItems + 1
        /\  UNCHANGED << Queues, PendingItems >>

Complete ==
    /\  ProcessedItems = Items
    /\  \A thread \in Threads: ThreadStates[thread].State = "Sleeping"
    /\  UNCHANGED vars

Next ==
    \E thread \in Threads :
        \/  Enqueue(thread)
        \/  Wakeup(thread)
        \* \/  Sleep(thread)
        \/  Process(thread)
        \/  Steal(thread)
        \/  ProcessItem(thread)
        \/  Complete

Spec ==
    /\  Init
    /\  [][Next]_vars

SpecWithFairness ==
    /\  Spec
    /\  \A thread \in Threads :
        /\  WF_vars(Enqueue(thread))
        /\  WF_vars(Process(thread))
        /\  WF_vars(
                ProcessItem(thread)
            )

AllItemsGetProcessed ==
    []<>(ProcessedItems = Items)

Alias == [
    ThreadStates |-> ThreadStates,
    Queues |-> Queues,
    PendingItems |-> PendingItems,
    ProcessedItems |-> ProcessedItems
]

=============================================================================
