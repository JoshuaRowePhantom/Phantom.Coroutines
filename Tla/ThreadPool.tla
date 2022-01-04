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
ThreadStatesType == [Threads -> { "Idle", "Enqueuing" }]
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
    /\  ThreadStates = [thread \in Threads |-> "Idle"]
    /\  Queues = [thread \in Threads |-> << >>]
    /\  Heads = [thread \in Threads |-> 1]
    /\  Tails =  [thread \in Threads |-> 1]
    /\  ProcessedItems = << >>

Enqueue ==
    \E item \in PendingItems :
    \E thread \in Threads :
        /\  ThreadStates[thread] = "Idle"
        /\  PendingItems' = PendingItems \ { item }
        /\  Queues' = [Queues EXCEPT ![thread] = Queues[thread] \o << item >>]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = "Enqueuing"]
        /\  UNCHANGED << Heads, Tails, ProcessedItems >>

FinishEnqueue ==
    \E thread \in Threads :
        /\  ThreadStates[thread] = "Enqueuing"
        /\  Heads' = [Heads EXCEPT ![thread] = Heads[thread] + 1]
        /\  ThreadStates' = [ThreadStates EXCEPT ![thread] = "Idle"]
        /\  UNCHANGED << PendingItems, Queues, Tails, ProcessedItems >>

Process ==
    \E thread \in Threads :
        /\  ThreadStates[thread] = "Idle"
        /\  Tails[thread] # Heads[thread]
        /\  Tails' = [Tails EXCEPT ![thread] = Tails[thread] + 1]
        /\  ProcessedItems' = ProcessedItems \o << Queues[thread][Tails[thread]] >>
        /\  UNCHANGED << PendingItems, Queues, Heads, ThreadStates >>

Steal ==
    \E stealingThread \in Threads :
    \E sourceThread \in Threads :
        /\  ThreadStates[stealingThread] = "Idle"
        /\  stealingThread # sourceThread
        /\  Tails[stealingThread] = Heads[stealingThread]
        /\  UNCHANGED << PendingItems, Queues, Heads, ProcessedItems >>
        
Next ==
    \/  Enqueue
    \/  FinishEnqueue
    \/  Process
    \* \/  Steal

Spec ==
    /\  Init
    /\  [][Next]_vars

SpecWithFairness ==
    /\  Spec
    /\  WF_vars(Process)
    /\  WF_vars(Enqueue)
    /\  WF_vars(FinishEnqueue)

AllItemsGetProcessed ==
    []<>(ProcessedItemsSet = Items)

NoItemIsProcessedInDuplicate ==
    Cardinality(DOMAIN(ProcessedItems)) = Cardinality(ProcessedItemsSet)

DebugEnabledActions ==
    [
        Enqueue |-> ENABLED(Enqueue),
        FinishEnqueue |-> ENABLED(FinishEnqueue),
        Process |-> ENABLED(Process)
    ]
         
=============================================================================
