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
  The head pointer is only modified by the thread owning the state.
* A tail pointer into the queue
  The tail pointer is modified by other threads executing Steal operations.
* A mutex
  The mutex is used to resolve conflicts when a thread dequeues and
  another thread attempts a steal.

The purpose behind this algorithm is to reduce the use of interlocked
operations. Most of the time, a thread can enqueue 
to itself and dequeue from itself with no interlocked operations. 

When a thread runs out of items, it attempts to steal from another thread.
Stealing requires a lock. 
When stealing, a thread can steal any quantity of items from the
source thread, but always processes at least one item without
enqueuing it locally. This guarantees forward progress, so that
multiple threads will not repeatedly steal from each other.
The purpose of stealing multiple items is to reduce the number of
interlocked operations; if a long-running work item is running
with many short work items queued behind it, the remaining
workers will contend on the thread with many items queued.
The actual copying of items from the source thread does not require a lock,
only the adjusting of head and tail pointers.
*)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT Threads, Items

RECURSIVE SetToSequence(_)
SetToSequence(S) ==
    IF S = {}
    THEN << >>
    ELSE 
        LET s == CHOOSE x \in S : TRUE 
        IN 
        << s >> \o SetToSequence(S \ {s})

(* --algorithm ThreadPool

variables
    PendingItems = SetToSequence(Items),
    Queues = [thread \in Threads |-> << >>],
    Heads = [thread \in Threads |-> 0],
    Tails =  [thread \in Threads |-> 0],
    ProcessedItems = { },
    Locks = [thread \in Threads |-> FALSE];

macro GoIdle()
begin
    ItemToProcess := {};
    SourceThreadTail := 0;
    SourceThreadHead := 0;
    SourceThreadCopyStart := 0;
    SourceThreadCopyEnd := 0;
    SourceThread := {};
end macro;

process thread \in Threads
variables 
    ItemToProcess = {}, 
    SourceThread = {},
    SourceThreadTail = 0,
    SourceThreadHead = 0,
    SourceThreadCopyStart = 0,
    SourceThreadCopyEnd = 0
begin
Idle:

    either
        await PendingItems # << >>;
        Queues[self] := (Heads[self] + 1) :> Head(PendingItems) @@ Queues[self];
        PendingItems := Tail(PendingItems);
        
        Enqueue_UpdateHead:
            Heads[self] := Heads[self] + 1;
            GoIdle();
            goto Idle;
        
    or
            Heads[self] := Heads[self] - 1;
        
        Process_ReadTail:
            if Tails[self] <= Heads[self] then
                ItemToProcess := { Queues[self][Heads[self] + 1 ] };
                goto ProcessItem;
            end if;

        ProcessInLock_Lock:
            await Locks[self] = FALSE;
            Locks[self] := TRUE;

        ProcessInLock_ReadTail:
            if Tails[self] > Heads[self] then
            ProcessInLock_IncrementHead:
                Heads[self] := Heads[self] + 1;
            ProcessInLock_UnlockOnIdle:
                Locks[self] := FALSE;
                GoIdle();
                goto Idle;
            end if;

        ProcessInLock_GetItemToProcess:
            ItemToProcess := { Queues[self][Heads[self] + 1] };
            Locks[self] := FALSE;
            goto ProcessItem;

    or

            with sourceThread \in (Threads \ { self }) do
                await Heads[self] = Tails[self];
                await Locks[sourceThread] = FALSE;

                \* This is an optimization for state space reduction
                await Heads[sourceThread] # Tails[sourceThread];

                SourceThread := sourceThread;
                Locks[sourceThread] := TRUE
            end with;

        Steal_ReadSourceThreadTail:
            SourceThreadTail := Tails[SourceThread];

        Steal_ReadSourceThreadHead:
            SourceThreadHead := Heads[SourceThread];

        Steal_UpdateTail:
            if SourceThreadTail >= SourceThreadHead then
                Locks[SourceThread] := FALSE;
                GoIdle();
                goto Idle;
            else
                with newTail \in SourceThreadTail + 1 .. SourceThreadHead do
                    Tails[SourceThread] := newTail;
                    SourceThreadCopyEnd := Tails[SourceThread];
                end with;
            end if;

        Steal_RereadHead:
            SourceThreadHead := Heads[SourceThread];

        Steal_AdjustTail:
            if SourceThreadHead <= SourceThreadTail then
                Tails[SourceThread] := SourceThreadTail;
                Locks[SourceThread] := FALSE;
                GoIdle();
                goto Idle;
            elsif SourceThreadHead < SourceThreadCopyEnd then
                SourceThreadCopyStart := SourceThreadTail;
                Tails[SourceThread] := SourceThreadHead;
                SourceThreadCopyEnd := SourceThreadHead;
            else
                SourceThreadCopyStart := SourceThreadTail;                
            end if;

        Steal_Unlock:
            Locks[SourceThread] := FALSE;

        Steal_Copy:
            while SourceThreadCopyStart < SourceThreadCopyEnd do
                Queues[self] := 
                    (Heads[self] + SourceThreadCopyStart - SourceThreadTail + 1) :> Queues[SourceThread][SourceThreadCopyStart + 1]
                    @@ Queues[self];
                SourceThreadCopyStart := SourceThreadCopyStart + 1;
            end while;

        Steal_UpdateHead:
            Heads[self] := Heads[self] + SourceThreadCopyEnd - SourceThreadTail - 1;
            ItemToProcess := { Queues[self][Heads[self] + 1] };
            goto ProcessItem;
    end either;

ProcessItem:
    ProcessedItems := ProcessedItems \union ItemToProcess;
    GoIdle();
    goto Idle;

end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "a82f425e" /\ chksum(tla) = "34ddb03f")
VARIABLES pc, PendingItems, Queues, Heads, Tails, ProcessedItems, Locks, 
          ItemToProcess, SourceThread, SourceThreadTail, SourceThreadHead, 
          SourceThreadCopyStart, SourceThreadCopyEnd

vars == << pc, PendingItems, Queues, Heads, Tails, ProcessedItems, Locks, 
           ItemToProcess, SourceThread, SourceThreadTail, SourceThreadHead, 
           SourceThreadCopyStart, SourceThreadCopyEnd >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ PendingItems = SetToSequence(Items)
        /\ Queues = [thread \in Threads |-> << >>]
        /\ Heads = [thread \in Threads |-> 0]
        /\ Tails = [thread \in Threads |-> 0]
        /\ ProcessedItems = { }
        /\ Locks = [thread \in Threads |-> FALSE]
        (* Process thread *)
        /\ ItemToProcess = [self \in Threads |-> {}]
        /\ SourceThread = [self \in Threads |-> {}]
        /\ SourceThreadTail = [self \in Threads |-> 0]
        /\ SourceThreadHead = [self \in Threads |-> 0]
        /\ SourceThreadCopyStart = [self \in Threads |-> 0]
        /\ SourceThreadCopyEnd = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "Idle"]

Idle(self) == /\ pc[self] = "Idle"
              /\ \/ /\ PendingItems # << >>
                    /\ Queues' = [Queues EXCEPT ![self] = (Heads[self] + 1) :> Head(PendingItems) @@ Queues[self]]
                    /\ PendingItems' = Tail(PendingItems)
                    /\ pc' = [pc EXCEPT ![self] = "Enqueue_UpdateHead"]
                    /\ UNCHANGED <<Heads, Locks, SourceThread>>
                 \/ /\ Heads' = [Heads EXCEPT ![self] = Heads[self] - 1]
                    /\ pc' = [pc EXCEPT ![self] = "Process_ReadTail"]
                    /\ UNCHANGED <<PendingItems, Queues, Locks, SourceThread>>
                 \/ /\ \E sourceThread \in (Threads \ { self }):
                         /\ Heads[self] = Tails[self]
                         /\ Locks[sourceThread] = FALSE
                         /\ Heads[sourceThread] # Tails[sourceThread]
                         /\ SourceThread' = [SourceThread EXCEPT ![self] = sourceThread]
                         /\ Locks' = [Locks EXCEPT ![sourceThread] = TRUE]
                    /\ pc' = [pc EXCEPT ![self] = "Steal_ReadSourceThreadTail"]
                    /\ UNCHANGED <<PendingItems, Queues, Heads>>
              /\ UNCHANGED << Tails, ProcessedItems, ItemToProcess, 
                              SourceThreadTail, SourceThreadHead, 
                              SourceThreadCopyStart, SourceThreadCopyEnd >>

Enqueue_UpdateHead(self) == /\ pc[self] = "Enqueue_UpdateHead"
                            /\ Heads' = [Heads EXCEPT ![self] = Heads[self] + 1]
                            /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = {}]
                            /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = 0]
                            /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = 0]
                            /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = 0]
                            /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = 0]
                            /\ SourceThread' = [SourceThread EXCEPT ![self] = {}]
                            /\ pc' = [pc EXCEPT ![self] = "Idle"]
                            /\ UNCHANGED << PendingItems, Queues, Tails, 
                                            ProcessedItems, Locks >>

Process_ReadTail(self) == /\ pc[self] = "Process_ReadTail"
                          /\ IF Tails[self] <= Heads[self]
                                THEN /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = { Queues[self][Heads[self] + 1 ] }]
                                     /\ pc' = [pc EXCEPT ![self] = "ProcessItem"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "ProcessInLock_Lock"]
                                     /\ UNCHANGED ItemToProcess
                          /\ UNCHANGED << PendingItems, Queues, Heads, Tails, 
                                          ProcessedItems, Locks, SourceThread, 
                                          SourceThreadTail, SourceThreadHead, 
                                          SourceThreadCopyStart, 
                                          SourceThreadCopyEnd >>

ProcessInLock_Lock(self) == /\ pc[self] = "ProcessInLock_Lock"
                            /\ Locks[self] = FALSE
                            /\ Locks' = [Locks EXCEPT ![self] = TRUE]
                            /\ pc' = [pc EXCEPT ![self] = "ProcessInLock_ReadTail"]
                            /\ UNCHANGED << PendingItems, Queues, Heads, Tails, 
                                            ProcessedItems, ItemToProcess, 
                                            SourceThread, SourceThreadTail, 
                                            SourceThreadHead, 
                                            SourceThreadCopyStart, 
                                            SourceThreadCopyEnd >>

ProcessInLock_ReadTail(self) == /\ pc[self] = "ProcessInLock_ReadTail"
                                /\ IF Tails[self] > Heads[self]
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ProcessInLock_IncrementHead"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ProcessInLock_GetItemToProcess"]
                                /\ UNCHANGED << PendingItems, Queues, Heads, 
                                                Tails, ProcessedItems, Locks, 
                                                ItemToProcess, SourceThread, 
                                                SourceThreadTail, 
                                                SourceThreadHead, 
                                                SourceThreadCopyStart, 
                                                SourceThreadCopyEnd >>

ProcessInLock_IncrementHead(self) == /\ pc[self] = "ProcessInLock_IncrementHead"
                                     /\ Heads' = [Heads EXCEPT ![self] = Heads[self] + 1]
                                     /\ pc' = [pc EXCEPT ![self] = "ProcessInLock_UnlockOnIdle"]
                                     /\ UNCHANGED << PendingItems, Queues, 
                                                     Tails, ProcessedItems, 
                                                     Locks, ItemToProcess, 
                                                     SourceThread, 
                                                     SourceThreadTail, 
                                                     SourceThreadHead, 
                                                     SourceThreadCopyStart, 
                                                     SourceThreadCopyEnd >>

ProcessInLock_UnlockOnIdle(self) == /\ pc[self] = "ProcessInLock_UnlockOnIdle"
                                    /\ Locks' = [Locks EXCEPT ![self] = FALSE]
                                    /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = {}]
                                    /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = 0]
                                    /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = 0]
                                    /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = 0]
                                    /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = 0]
                                    /\ SourceThread' = [SourceThread EXCEPT ![self] = {}]
                                    /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                    /\ UNCHANGED << PendingItems, Queues, 
                                                    Heads, Tails, 
                                                    ProcessedItems >>

ProcessInLock_GetItemToProcess(self) == /\ pc[self] = "ProcessInLock_GetItemToProcess"
                                        /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = { Queues[self][Heads[self] + 1] }]
                                        /\ Locks' = [Locks EXCEPT ![self] = FALSE]
                                        /\ pc' = [pc EXCEPT ![self] = "ProcessItem"]
                                        /\ UNCHANGED << PendingItems, Queues, 
                                                        Heads, Tails, 
                                                        ProcessedItems, 
                                                        SourceThread, 
                                                        SourceThreadTail, 
                                                        SourceThreadHead, 
                                                        SourceThreadCopyStart, 
                                                        SourceThreadCopyEnd >>

Steal_ReadSourceThreadTail(self) == /\ pc[self] = "Steal_ReadSourceThreadTail"
                                    /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = Tails[SourceThread[self]]]
                                    /\ pc' = [pc EXCEPT ![self] = "Steal_ReadSourceThreadHead"]
                                    /\ UNCHANGED << PendingItems, Queues, 
                                                    Heads, Tails, 
                                                    ProcessedItems, Locks, 
                                                    ItemToProcess, 
                                                    SourceThread, 
                                                    SourceThreadHead, 
                                                    SourceThreadCopyStart, 
                                                    SourceThreadCopyEnd >>

Steal_ReadSourceThreadHead(self) == /\ pc[self] = "Steal_ReadSourceThreadHead"
                                    /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = Heads[SourceThread[self]]]
                                    /\ pc' = [pc EXCEPT ![self] = "Steal_UpdateTail"]
                                    /\ UNCHANGED << PendingItems, Queues, 
                                                    Heads, Tails, 
                                                    ProcessedItems, Locks, 
                                                    ItemToProcess, 
                                                    SourceThread, 
                                                    SourceThreadTail, 
                                                    SourceThreadCopyStart, 
                                                    SourceThreadCopyEnd >>

Steal_UpdateTail(self) == /\ pc[self] = "Steal_UpdateTail"
                          /\ IF SourceThreadTail[self] >= SourceThreadHead[self]
                                THEN /\ Locks' = [Locks EXCEPT ![SourceThread[self]] = FALSE]
                                     /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = {}]
                                     /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = 0]
                                     /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = 0]
                                     /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = 0]
                                     /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = 0]
                                     /\ SourceThread' = [SourceThread EXCEPT ![self] = {}]
                                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                     /\ Tails' = Tails
                                ELSE /\ \E newTail \in SourceThreadTail[self] + 1 .. SourceThreadHead[self]:
                                          /\ Tails' = [Tails EXCEPT ![SourceThread[self]] = newTail]
                                          /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = Tails'[SourceThread[self]]]
                                     /\ pc' = [pc EXCEPT ![self] = "Steal_RereadHead"]
                                     /\ UNCHANGED << Locks, ItemToProcess, 
                                                     SourceThread, 
                                                     SourceThreadTail, 
                                                     SourceThreadHead, 
                                                     SourceThreadCopyStart >>
                          /\ UNCHANGED << PendingItems, Queues, Heads, 
                                          ProcessedItems >>

Steal_RereadHead(self) == /\ pc[self] = "Steal_RereadHead"
                          /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = Heads[SourceThread[self]]]
                          /\ pc' = [pc EXCEPT ![self] = "Steal_AdjustTail"]
                          /\ UNCHANGED << PendingItems, Queues, Heads, Tails, 
                                          ProcessedItems, Locks, ItemToProcess, 
                                          SourceThread, SourceThreadTail, 
                                          SourceThreadCopyStart, 
                                          SourceThreadCopyEnd >>

Steal_AdjustTail(self) == /\ pc[self] = "Steal_AdjustTail"
                          /\ IF SourceThreadHead[self] <= SourceThreadTail[self]
                                THEN /\ Tails' = [Tails EXCEPT ![SourceThread[self]] = SourceThreadTail[self]]
                                     /\ Locks' = [Locks EXCEPT ![SourceThread[self]] = FALSE]
                                     /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = {}]
                                     /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = 0]
                                     /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = 0]
                                     /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = 0]
                                     /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = 0]
                                     /\ SourceThread' = [SourceThread EXCEPT ![self] = {}]
                                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                                ELSE /\ IF SourceThreadHead[self] < SourceThreadCopyEnd[self]
                                           THEN /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = SourceThreadTail[self]]
                                                /\ Tails' = [Tails EXCEPT ![SourceThread[self]] = SourceThreadHead[self]]
                                                /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = SourceThreadHead[self]]
                                           ELSE /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = SourceThreadTail[self]]
                                                /\ UNCHANGED << Tails, 
                                                                SourceThreadCopyEnd >>
                                     /\ pc' = [pc EXCEPT ![self] = "Steal_Unlock"]
                                     /\ UNCHANGED << Locks, ItemToProcess, 
                                                     SourceThread, 
                                                     SourceThreadTail, 
                                                     SourceThreadHead >>
                          /\ UNCHANGED << PendingItems, Queues, Heads, 
                                          ProcessedItems >>

Steal_Unlock(self) == /\ pc[self] = "Steal_Unlock"
                      /\ Locks' = [Locks EXCEPT ![SourceThread[self]] = FALSE]
                      /\ pc' = [pc EXCEPT ![self] = "Steal_Copy"]
                      /\ UNCHANGED << PendingItems, Queues, Heads, Tails, 
                                      ProcessedItems, ItemToProcess, 
                                      SourceThread, SourceThreadTail, 
                                      SourceThreadHead, SourceThreadCopyStart, 
                                      SourceThreadCopyEnd >>

Steal_Copy(self) == /\ pc[self] = "Steal_Copy"
                    /\ IF SourceThreadCopyStart[self] < SourceThreadCopyEnd[self]
                          THEN /\ Queues' = [Queues EXCEPT ![self] = (Heads[self] + SourceThreadCopyStart[self] - SourceThreadTail[self] + 1) :> Queues[SourceThread[self]][SourceThreadCopyStart[self] + 1]
                                                                     @@ Queues[self]]
                               /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = SourceThreadCopyStart[self] + 1]
                               /\ pc' = [pc EXCEPT ![self] = "Steal_Copy"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Steal_UpdateHead"]
                               /\ UNCHANGED << Queues, SourceThreadCopyStart >>
                    /\ UNCHANGED << PendingItems, Heads, Tails, ProcessedItems, 
                                    Locks, ItemToProcess, SourceThread, 
                                    SourceThreadTail, SourceThreadHead, 
                                    SourceThreadCopyEnd >>

Steal_UpdateHead(self) == /\ pc[self] = "Steal_UpdateHead"
                          /\ Heads' = [Heads EXCEPT ![self] = Heads[self] + SourceThreadCopyEnd[self] - SourceThreadTail[self] - 1]
                          /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = { Queues[self][Heads'[self] + 1] }]
                          /\ pc' = [pc EXCEPT ![self] = "ProcessItem"]
                          /\ UNCHANGED << PendingItems, Queues, Tails, 
                                          ProcessedItems, Locks, SourceThread, 
                                          SourceThreadTail, SourceThreadHead, 
                                          SourceThreadCopyStart, 
                                          SourceThreadCopyEnd >>

ProcessItem(self) == /\ pc[self] = "ProcessItem"
                     /\ ProcessedItems' = (ProcessedItems \union ItemToProcess[self])
                     /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = {}]
                     /\ SourceThreadTail' = [SourceThreadTail EXCEPT ![self] = 0]
                     /\ SourceThreadHead' = [SourceThreadHead EXCEPT ![self] = 0]
                     /\ SourceThreadCopyStart' = [SourceThreadCopyStart EXCEPT ![self] = 0]
                     /\ SourceThreadCopyEnd' = [SourceThreadCopyEnd EXCEPT ![self] = 0]
                     /\ SourceThread' = [SourceThread EXCEPT ![self] = {}]
                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                     /\ UNCHANGED << PendingItems, Queues, Heads, Tails, Locks >>

thread(self) == Idle(self) \/ Enqueue_UpdateHead(self)
                   \/ Process_ReadTail(self) \/ ProcessInLock_Lock(self)
                   \/ ProcessInLock_ReadTail(self)
                   \/ ProcessInLock_IncrementHead(self)
                   \/ ProcessInLock_UnlockOnIdle(self)
                   \/ ProcessInLock_GetItemToProcess(self)
                   \/ Steal_ReadSourceThreadTail(self)
                   \/ Steal_ReadSourceThreadHead(self)
                   \/ Steal_UpdateTail(self) \/ Steal_RereadHead(self)
                   \/ Steal_AdjustTail(self) \/ Steal_Unlock(self)
                   \/ Steal_Copy(self) \/ Steal_UpdateHead(self)
                   \/ ProcessItem(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

PendingItemsType == Seq(Items)
QueuesType == [Threads -> Seq(Items)]
HeadsType == [Threads -> Int]
TailsType == [Threads -> Nat]
ProcessedItemsType == SUBSET Items
LocksType == [Threads -> BOOLEAN ]
ItemToProcessType == [Threads -> { itemsSet \in SUBSET Items : Cardinality(itemsSet) <= 1 } ]

TypeOk ==
    /\  PendingItems \in PendingItemsType
    /\  Queues \in QueuesType
    /\  Heads \in HeadsType
    /\  Tails \in TailsType
    /\  ProcessedItems \in ProcessedItemsType
    /\  ItemToProcess \in ItemToProcessType

IsComplete ==
        /\  PendingItems = << >>
        /\  ProcessedItems = Items

SpecWithFairness ==
    /\  Spec
    /\  \A self \in Threads :
        /\  SF_vars(Idle(self))
        /\  SF_vars(Idle(self) /\ Heads'[self] # Heads[self])
        /\  SF_vars(Idle(self) /\ PendingItems' # PendingItems)
        /\  WF_vars(Enqueue_UpdateHead(self))
        /\  WF_vars(Process_ReadTail(self))
        /\  SF_vars(ProcessInLock_Lock(self))
        /\  WF_vars(ProcessInLock_ReadTail(self))
        /\  WF_vars(ProcessInLock_GetItemToProcess(self))
        /\  WF_vars(ProcessInLock_IncrementHead(self))
        /\  WF_vars(ProcessInLock_UnlockOnIdle(self))
        /\  WF_vars(Steal_ReadSourceThreadTail(self))
        /\  WF_vars(Steal_ReadSourceThreadHead(self))
        /\  WF_vars(Steal_Copy(self))
        /\  WF_vars(Steal_UpdateTail(self))
        /\  WF_vars(Steal_RereadHead(self))
        /\  WF_vars(Steal_AdjustTail(self))
        /\  WF_vars(Steal_Unlock(self))
        /\  WF_vars(Steal_Copy(self))
        /\  WF_vars(Steal_UpdateHead(self))
        /\  WF_vars(ProcessItem(self))

AllItemsGetProcessed ==
    []<>(IsComplete)

NoItemIsProcessedInDuplicate ==
    \A self \in Threads : ItemToProcess[self] \intersect ProcessedItems = {}

Symmetry == Permutations(Threads) \union Permutations(Items)
  
=============================================================================
