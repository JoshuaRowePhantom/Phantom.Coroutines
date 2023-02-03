---- MODULE FairReaderWriterLock_AtomicState_Queue ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    LockCount,
    PendingLockDecrementCount,

    \* These three variables can be atomically read-modify-written.
    ResumeLock,
    LockState,
    Queue,
    HasPendingDecrements,

    Pending,
    Locks,
    Destroyed,
    locksToResume,
    lockToUnlock,
    lockToEnqueue

AbstractLocks ==
    Locks
    \union
    UNION
    {
        {
            locksToResume[thread][index]
            :
            index \in 1..Len(locksToResume[thread])
        }
        :
        thread \in Threads
    }

AbstractQueue ==
    Pending \o Queue

FairLock == 
    INSTANCE FairReaderWriterLock
    WITH 
    Locks <- AbstractLocks,
    Queue <- AbstractQueue

LockType == FairLock!LockType

AllThreads == Threads \union { "Destroyer" }

TypeOk ==
    /\  LockCount \in 0..Cardinality(Threads)*2
    /\  PendingLockDecrementCount \in 0..Cardinality(Threads)
    /\  HasPendingDecrements \in BOOLEAN
    /\  ResumeLock \in { "Unlocked", "Resuming" }
    /\  LockState \in { "Read", "Write", "Unlocked" }
    /\  Queue \in FairLock!QueueType
    /\  Locks \in SUBSET LockType
    /\  Destroyed \in BOOLEAN

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

LocksAreCompatible(lock1, lock2) == 
    \/  /\  lock1.Type = "Read"
        /\  lock2.Type = "Read"
    \/  lock1 = lock2

CanDestroy ==
    /\  \A thread \in Threads :
        /\  lockToEnqueue[thread] = << >>
        /\  lockToUnlock[thread] = << >>
    /\  AbstractLocks = { }
    /\  Queue = << >>
    /\  Pending = << >>

IsLockRequest(request, type) == request # << >> /\ request[1].Type = type
IsWriteRequest(request) == IsLockRequest(request, "Write")
IsReadRequest(request) == IsLockRequest(request, "Read")

(* --algorithm FairReaderWriterLock_AtomicState_Queue

variables
    \* 0 = unlocked or locked for read
    \* > 0 = # of readers
    LockCount = 0,
    PendingLockDecrementCount = 0,
    HasPendingDecrements = FALSE,
    ResumeLock = "Unlocked",
    LockState = "Unlocked",
    Queue = << >>,
    Pending = << >>,
    Locks = { },
    Destroyed = FALSE;

macro AddLock(lock)
begin
    Locks := Locks \union { lock };
end macro;

macro Unlock(lock)
begin
    Locks := Locks \ { lock };
end macro;

macro AddWaiter(lock)
begin
    Queue :=  Queue \o << lock >>;
    State := State;
end macro;

procedure UpdateLockState(
    lockToEnqueue = << >>,
    lockToUnlock = << >>
)
variable 
    locksToResume = << >>,
    unservedPendingDecrements = 0,
    nextLockState = "",
    previousLockState = ""
begin
IncrementPendingDecrementCount:
    assert Len(lockToEnqueue \o lockToUnlock) = 1;
    assert ~Destroyed;
    if IsReadRequest(lockToUnlock) then
        PendingLockDecrementCount := PendingLockDecrementCount + 1;
    end if;

EnqueueLock:
    assert ~Destroyed;
    
    if  ResumeLock = "Resuming" /\ LockState = "Write" /\ IsWriteRequest(lockToUnlock) then
        LockState := "Unlocked";
        lockToUnlock := << >>;
        HasPendingDecrements := TRUE;
        goto ResumeLocks;
    elsif ResumeLock = "Resuming" then
        Queue := Queue \o lockToEnqueue;
        lockToEnqueue := << >>;
        HasPendingDecrements := HasPendingDecrements \/ IsReadRequest(lockToUnlock);
        goto ResumeLocks;
    elsif 
        \/  LockState = "Write" /\ lockToEnqueue # << >>
        \/  LockState = "Read" /\ IsWriteRequest(lockToEnqueue) then
        Queue := Queue \o lockToEnqueue;
        lockToEnqueue := << >>;
        goto ResumeLocks;
    else
        ResumeLock := "Resuming";
        if IsWriteRequest(lockToUnlock) then
            nextLockState := "Unlocked";
        else
            nextLockState := LockState;
        end if;
        \* This set to Pending is not atomic, but we don't require atomicity for
        \* assignments to atomic. We atomically exchange the queue for empty,
        \* then non-atomically add the items in the queue to Pending.
        \* In a real implementation, we appended to queue by writing to the list head,
        \* and the assignment to Pending traverses the queue and reverses the Queue
        \* while appending to Pending.
        Pending := Pending \o Queue \o lockToEnqueue;
        HasPendingDecrements := FALSE;
        Queue := << >>;
        lockToEnqueue := << >>;
        previousLockState := LockState;
        goto ReadPendingDecrements;
    end if;

ReadPendingDecrements:
    assert ~Destroyed;
    unservedPendingDecrements := PendingLockDecrementCount;
    PendingLockDecrementCount := 0;
    
    if unservedPendingDecrements > 0 then
ServicePendingDecrements:
        LockCount := LockCount - unservedPendingDecrements;
        unservedPendingDecrements := 0;
        if LockCount = 0 then
            previousLockState := "Unlocked";
            nextLockState := "Unlocked";
        end if;
    end if;

CollectPendingLocks:
    assert ~Destroyed;
    with 
        allPendingLocks = locksToResume \o Pending,
        index \in 0..Len(Pending)
        do

        locksToResume := locksToResume \o SubSeq(Pending, 1, index);

        await 
            /\  \A otherIndex \in 1..index :
                /\  LocksAreCompatible(locksToResume[1], Pending[otherIndex])
            /\  ~ \E otherIndex \in (index + 1)..Len(Pending) :
                /\  otherIndex = index + 1
                /\  locksToResume # << >>
                /\  LocksAreCompatible(locksToResume[1], Pending[otherIndex])
            /\  (locksToResume = << >>) =>
                    (allPendingLocks # << >> =>
                        \/  nextLockState = "Read" /\ allPendingLocks[1].Type = "Write"
                        \/  nextLockState = "Write" /\ allPendingLocks[1].Type = "Read");

        if locksToResume # << >> then
            nextLockState := locksToResume[1].Type;
            if locksToResume[1].Type = "Read" then
                LockCount := LockCount + index;
            end if;
        end if;

        Pending := SubSeq(Pending, index + 1, Len(Pending));

    end with;

CheckResumeLock:
    assert ~Destroyed;
    if HasPendingDecrements \/ Queue # << >> then
        HasPendingDecrements := FALSE;
        Pending := Pending \o Queue;
        Queue := << >>;
        ResumeLock := "Resuming";
        previousLockState := LockState;
        goto ReadPendingDecrements;
    elsif Queue # << >> then
        Pending := Pending \o Queue;
        Queue := << >>;
        nextLockState := LockState;
        previousLockState := LockState;
        goto CollectPendingLocks;
    elsif LockState = "Unlocked" /\ locksToResume = << >> then
        LockState := "Unlocked";
        ResumeLock := "Unlocked";
        nextLockState := "";
        previousLockState := "";
    else
        LockState := nextLockState;
        ResumeLock := "Unlocked";
        nextLockState := "";
        previousLockState := "";
    end if;

ResumeLocks:
    while locksToResume # << >> do
        locksToResume := Tail(locksToResume)
        ||
        Locks := Locks \union { Head(locksToResume) };
    end while;
    return;

end procedure;

fair process Thread \in Threads
begin
Lock:
    either 
        await Destroyed;
    or
    await ~Destroyed;
    either
        \* Become a reader.
        assert ~Destroyed;
        call UpdateLockState(
            << ReadLock(self) >>,
            << >>
        );

Unlock_Read:
        assert ~Destroyed;
        await ReadLock(self) \in Locks;

        Locks := Locks \ { ReadLock(self) };
        call UpdateLockState(
            << >>,
            << ReadLock(self) >>);
        goto Lock;

    or
        \* Enqueue for write
        call UpdateLockState(
            << WriteLock(self) >>,
            << >>);

Unlock_Write:
        assert ~Destroyed;
        await WriteLock(self) \in Locks;

        Locks := Locks \ { WriteLock(self) };
        call UpdateLockState(
            << >>,
            << WriteLock(self) >>);
        goto Lock;

    end either;
    end either;
end process;

fair process Destroy \in { "Destroyer" }
begin
DestroyIfIdle:
    await CanDestroy;
    Destroyed := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9146df85" /\ chksum(tla) = "9a6f8ced")
VARIABLES LockCount, PendingLockDecrementCount, HasPendingDecrements, 
          ResumeLock, LockState, Queue, Pending, Locks, Destroyed, pc, stack, 
          lockToEnqueue, lockToUnlock, locksToResume, 
          unservedPendingDecrements, nextLockState, previousLockState

vars == << LockCount, PendingLockDecrementCount, HasPendingDecrements, 
           ResumeLock, LockState, Queue, Pending, Locks, Destroyed, pc, stack, 
           lockToEnqueue, lockToUnlock, locksToResume, 
           unservedPendingDecrements, nextLockState, previousLockState >>

ProcSet == (Threads) \cup ({ "Destroyer" })

Init == (* Global variables *)
        /\ LockCount = 0
        /\ PendingLockDecrementCount = 0
        /\ HasPendingDecrements = FALSE
        /\ ResumeLock = "Unlocked"
        /\ LockState = "Unlocked"
        /\ Queue = << >>
        /\ Pending = << >>
        /\ Locks = { }
        /\ Destroyed = FALSE
        (* Procedure UpdateLockState *)
        /\ lockToEnqueue = [ self \in ProcSet |-> << >>]
        /\ lockToUnlock = [ self \in ProcSet |-> << >>]
        /\ locksToResume = [ self \in ProcSet |-> << >>]
        /\ unservedPendingDecrements = [ self \in ProcSet |-> 0]
        /\ nextLockState = [ self \in ProcSet |-> ""]
        /\ previousLockState = [ self \in ProcSet |-> ""]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Lock"
                                        [] self \in { "Destroyer" } -> "DestroyIfIdle"]

IncrementPendingDecrementCount(self) == /\ pc[self] = "IncrementPendingDecrementCount"
                                        /\ Assert(Len(lockToEnqueue[self] \o lockToUnlock[self]) = 1, 
                                                  "Failure of assertion at line 122, column 5.")
                                        /\ Assert(~Destroyed, 
                                                  "Failure of assertion at line 123, column 5.")
                                        /\ IF IsReadRequest(lockToUnlock[self])
                                              THEN /\ PendingLockDecrementCount' = PendingLockDecrementCount + 1
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED PendingLockDecrementCount
                                        /\ pc' = [pc EXCEPT ![self] = "EnqueueLock"]
                                        /\ UNCHANGED << LockCount, 
                                                        HasPendingDecrements, 
                                                        ResumeLock, LockState, 
                                                        Queue, Pending, Locks, 
                                                        Destroyed, stack, 
                                                        lockToEnqueue, 
                                                        lockToUnlock, 
                                                        locksToResume, 
                                                        unservedPendingDecrements, 
                                                        nextLockState, 
                                                        previousLockState >>

EnqueueLock(self) == /\ pc[self] = "EnqueueLock"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 129, column 5.")
                     /\ IF ResumeLock = "Resuming" /\ LockState = "Write" /\ IsWriteRequest(lockToUnlock[self])
                           THEN /\ LockState' = "Unlocked"
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                                /\ HasPendingDecrements' = TRUE
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED << ResumeLock, Queue, Pending, 
                                                lockToEnqueue, nextLockState, 
                                                previousLockState >>
                           ELSE /\ IF ResumeLock = "Resuming"
                                      THEN /\ Queue' = Queue \o lockToEnqueue[self]
                                           /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                                           /\ HasPendingDecrements' = (HasPendingDecrements \/ IsReadRequest(lockToUnlock[self]))
                                           /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                           /\ UNCHANGED << ResumeLock, Pending, 
                                                           nextLockState, 
                                                           previousLockState >>
                                      ELSE /\ IF \/  LockState = "Write" /\ lockToEnqueue[self] # << >>
                                                 \/  LockState = "Read" /\ IsWriteRequest(lockToEnqueue[self])
                                                 THEN /\ Queue' = Queue \o lockToEnqueue[self]
                                                      /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                                                      /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                                      /\ UNCHANGED << HasPendingDecrements, 
                                                                      ResumeLock, 
                                                                      Pending, 
                                                                      nextLockState, 
                                                                      previousLockState >>
                                                 ELSE /\ ResumeLock' = "Resuming"
                                                      /\ IF IsWriteRequest(lockToUnlock[self])
                                                            THEN /\ nextLockState' = [nextLockState EXCEPT ![self] = "Unlocked"]
                                                            ELSE /\ nextLockState' = [nextLockState EXCEPT ![self] = LockState]
                                                      /\ Pending' = Pending \o Queue \o lockToEnqueue[self]
                                                      /\ HasPendingDecrements' = FALSE
                                                      /\ Queue' = << >>
                                                      /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                                                      /\ previousLockState' = [previousLockState EXCEPT ![self] = LockState]
                                                      /\ pc' = [pc EXCEPT ![self] = "ReadPendingDecrements"]
                                /\ UNCHANGED << LockState, lockToUnlock >>
                     /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                     Locks, Destroyed, stack, locksToResume, 
                                     unservedPendingDecrements >>

ReadPendingDecrements(self) == /\ pc[self] = "ReadPendingDecrements"
                               /\ Assert(~Destroyed, 
                                         "Failure of assertion at line 169, column 5.")
                               /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = PendingLockDecrementCount]
                               /\ PendingLockDecrementCount' = 0
                               /\ IF unservedPendingDecrements'[self] > 0
                                     THEN /\ pc' = [pc EXCEPT ![self] = "ServicePendingDecrements"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "CollectPendingLocks"]
                               /\ UNCHANGED << LockCount, HasPendingDecrements, 
                                               ResumeLock, LockState, Queue, 
                                               Pending, Locks, Destroyed, 
                                               stack, lockToEnqueue, 
                                               lockToUnlock, locksToResume, 
                                               nextLockState, 
                                               previousLockState >>

ServicePendingDecrements(self) == /\ pc[self] = "ServicePendingDecrements"
                                  /\ LockCount' = LockCount - unservedPendingDecrements[self]
                                  /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = 0]
                                  /\ IF LockCount' = 0
                                        THEN /\ previousLockState' = [previousLockState EXCEPT ![self] = "Unlocked"]
                                             /\ nextLockState' = [nextLockState EXCEPT ![self] = "Unlocked"]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << nextLockState, 
                                                             previousLockState >>
                                  /\ pc' = [pc EXCEPT ![self] = "CollectPendingLocks"]
                                  /\ UNCHANGED << PendingLockDecrementCount, 
                                                  HasPendingDecrements, 
                                                  ResumeLock, LockState, Queue, 
                                                  Pending, Locks, Destroyed, 
                                                  stack, lockToEnqueue, 
                                                  lockToUnlock, locksToResume >>

CollectPendingLocks(self) == /\ pc[self] = "CollectPendingLocks"
                             /\ Assert(~Destroyed, 
                                       "Failure of assertion at line 184, column 5.")
                             /\ LET allPendingLocks == locksToResume[self] \o Pending IN
                                  \E index \in 0..Len(Pending):
                                    /\ locksToResume' = [locksToResume EXCEPT ![self] = locksToResume[self] \o SubSeq(Pending, 1, index)]
                                    /\ /\  \A otherIndex \in 1..index :
                                           /\  LocksAreCompatible(locksToResume'[self][1], Pending[otherIndex])
                                       /\  ~ \E otherIndex \in (index + 1)..Len(Pending) :
                                           /\  otherIndex = index + 1
                                           /\  locksToResume'[self] # << >>
                                           /\  LocksAreCompatible(locksToResume'[self][1], Pending[otherIndex])
                                       /\  (locksToResume'[self] = << >>) =>
                                               (allPendingLocks # << >> =>
                                                   \/  nextLockState[self] = "Read" /\ allPendingLocks[1].Type = "Write"
                                                   \/  nextLockState[self] = "Write" /\ allPendingLocks[1].Type = "Read")
                                    /\ IF locksToResume'[self] # << >>
                                          THEN /\ nextLockState' = [nextLockState EXCEPT ![self] = locksToResume'[self][1].Type]
                                               /\ IF locksToResume'[self][1].Type = "Read"
                                                     THEN /\ LockCount' = LockCount + index
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED LockCount
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << LockCount, 
                                                               nextLockState >>
                                    /\ Pending' = SubSeq(Pending, index + 1, Len(Pending))
                             /\ pc' = [pc EXCEPT ![self] = "CheckResumeLock"]
                             /\ UNCHANGED << PendingLockDecrementCount, 
                                             HasPendingDecrements, ResumeLock, 
                                             LockState, Queue, Locks, 
                                             Destroyed, stack, lockToEnqueue, 
                                             lockToUnlock, 
                                             unservedPendingDecrements, 
                                             previousLockState >>

CheckResumeLock(self) == /\ pc[self] = "CheckResumeLock"
                         /\ Assert(~Destroyed, 
                                   "Failure of assertion at line 216, column 5.")
                         /\ IF HasPendingDecrements \/ Queue # << >>
                               THEN /\ HasPendingDecrements' = FALSE
                                    /\ Pending' = Pending \o Queue
                                    /\ Queue' = << >>
                                    /\ ResumeLock' = "Resuming"
                                    /\ previousLockState' = [previousLockState EXCEPT ![self] = LockState]
                                    /\ pc' = [pc EXCEPT ![self] = "ReadPendingDecrements"]
                                    /\ UNCHANGED << LockState, nextLockState >>
                               ELSE /\ IF Queue # << >>
                                          THEN /\ Pending' = Pending \o Queue
                                               /\ Queue' = << >>
                                               /\ nextLockState' = [nextLockState EXCEPT ![self] = LockState]
                                               /\ previousLockState' = [previousLockState EXCEPT ![self] = LockState]
                                               /\ pc' = [pc EXCEPT ![self] = "CollectPendingLocks"]
                                               /\ UNCHANGED << ResumeLock, 
                                                               LockState >>
                                          ELSE /\ IF LockState = "Unlocked" /\ locksToResume[self] = << >>
                                                     THEN /\ LockState' = "Unlocked"
                                                          /\ ResumeLock' = "Unlocked"
                                                          /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                                                          /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                                                     ELSE /\ LockState' = nextLockState[self]
                                                          /\ ResumeLock' = "Unlocked"
                                                          /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                                                          /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                                               /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                               /\ UNCHANGED << Queue, Pending >>
                                    /\ UNCHANGED HasPendingDecrements
                         /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                         Locks, Destroyed, stack, 
                                         lockToEnqueue, lockToUnlock, 
                                         locksToResume, 
                                         unservedPendingDecrements >>

ResumeLocks(self) == /\ pc[self] = "ResumeLocks"
                     /\ IF locksToResume[self] # << >>
                           THEN /\ /\ Locks' = (Locks \union { Head(locksToResume[self]) })
                                   /\ locksToResume' = [locksToResume EXCEPT ![self] = Tail(locksToResume[self])]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED << stack, lockToEnqueue, 
                                                lockToUnlock, 
                                                unservedPendingDecrements, 
                                                nextLockState, 
                                                previousLockState >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Head(stack[self]).locksToResume]
                                /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = Head(stack[self]).unservedPendingDecrements]
                                /\ nextLockState' = [nextLockState EXCEPT ![self] = Head(stack[self]).nextLockState]
                                /\ previousLockState' = [previousLockState EXCEPT ![self] = Head(stack[self]).previousLockState]
                                /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = Head(stack[self]).lockToEnqueue]
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = Head(stack[self]).lockToUnlock]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ Locks' = Locks
                     /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                     HasPendingDecrements, ResumeLock, 
                                     LockState, Queue, Pending, Destroyed >>

UpdateLockState(self) == IncrementPendingDecrementCount(self)
                            \/ EnqueueLock(self)
                            \/ ReadPendingDecrements(self)
                            \/ ServicePendingDecrements(self)
                            \/ CollectPendingLocks(self)
                            \/ CheckResumeLock(self) \/ ResumeLocks(self)

Lock(self) == /\ pc[self] = "Lock"
              /\ \/ /\ Destroyed
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED <<stack, lockToEnqueue, lockToUnlock, locksToResume, unservedPendingDecrements, nextLockState, previousLockState>>
                 \/ /\ ~Destroyed
                    /\ \/ /\ Assert(~Destroyed, 
                                    "Failure of assertion at line 261, column 9.")
                          /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << ReadLock(self) >>]
                             /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                      pc        |->  "Unlock_Read",
                                                                      locksToResume |->  locksToResume[self],
                                                                      unservedPendingDecrements |->  unservedPendingDecrements[self],
                                                                      nextLockState |->  nextLockState[self],
                                                                      previousLockState |->  previousLockState[self],
                                                                      lockToEnqueue |->  lockToEnqueue[self],
                                                                      lockToUnlock |->  lockToUnlock[self] ] >>
                                                                  \o stack[self]]
                          /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                          /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = 0]
                          /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                          /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                          /\ pc' = [pc EXCEPT ![self] = "IncrementPendingDecrementCount"]
                       \/ /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << WriteLock(self) >>]
                             /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                      pc        |->  "Unlock_Write",
                                                                      locksToResume |->  locksToResume[self],
                                                                      unservedPendingDecrements |->  unservedPendingDecrements[self],
                                                                      nextLockState |->  nextLockState[self],
                                                                      previousLockState |->  previousLockState[self],
                                                                      lockToEnqueue |->  lockToEnqueue[self],
                                                                      lockToUnlock |->  lockToUnlock[self] ] >>
                                                                  \o stack[self]]
                          /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                          /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = 0]
                          /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                          /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                          /\ pc' = [pc EXCEPT ![self] = "IncrementPendingDecrementCount"]
              /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                              HasPendingDecrements, ResumeLock, LockState, 
                              Queue, Pending, Locks, Destroyed >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 268, column 9.")
                     /\ ReadLock(self) \in Locks
                     /\ Locks' = Locks \ { ReadLock(self) }
                     /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                        /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << ReadLock(self) >>]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                 pc        |->  "Lock",
                                                                 locksToResume |->  locksToResume[self],
                                                                 unservedPendingDecrements |->  unservedPendingDecrements[self],
                                                                 nextLockState |->  nextLockState[self],
                                                                 previousLockState |->  previousLockState[self],
                                                                 lockToEnqueue |->  lockToEnqueue[self],
                                                                 lockToUnlock |->  lockToUnlock[self] ] >>
                                                             \o stack[self]]
                     /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                     /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = 0]
                     /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                     /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                     /\ pc' = [pc EXCEPT ![self] = "IncrementPendingDecrementCount"]
                     /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                     HasPendingDecrements, ResumeLock, 
                                     LockState, Queue, Pending, Destroyed >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ Assert(~Destroyed, 
                                "Failure of assertion at line 284, column 9.")
                      /\ WriteLock(self) \in Locks
                      /\ Locks' = Locks \ { WriteLock(self) }
                      /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                         /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << WriteLock(self) >>]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                  pc        |->  "Lock",
                                                                  locksToResume |->  locksToResume[self],
                                                                  unservedPendingDecrements |->  unservedPendingDecrements[self],
                                                                  nextLockState |->  nextLockState[self],
                                                                  previousLockState |->  previousLockState[self],
                                                                  lockToEnqueue |->  lockToEnqueue[self],
                                                                  lockToUnlock |->  lockToUnlock[self] ] >>
                                                              \o stack[self]]
                      /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                      /\ unservedPendingDecrements' = [unservedPendingDecrements EXCEPT ![self] = 0]
                      /\ nextLockState' = [nextLockState EXCEPT ![self] = ""]
                      /\ previousLockState' = [previousLockState EXCEPT ![self] = ""]
                      /\ pc' = [pc EXCEPT ![self] = "IncrementPendingDecrementCount"]
                      /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                      HasPendingDecrements, ResumeLock, 
                                      LockState, Queue, Pending, Destroyed >>

Thread(self) == Lock(self) \/ Unlock_Read(self) \/ Unlock_Write(self)

DestroyIfIdle(self) == /\ pc[self] = "DestroyIfIdle"
                       /\ CanDestroy
                       /\ Destroyed' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << LockCount, PendingLockDecrementCount, 
                                       HasPendingDecrements, ResumeLock, 
                                       LockState, Queue, Pending, Locks, stack, 
                                       lockToEnqueue, lockToUnlock, 
                                       locksToResume, 
                                       unservedPendingDecrements, 
                                       nextLockState, previousLockState >>

Destroy(self) == DestroyIfIdle(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: UpdateLockState(self))
           \/ (\E self \in Threads: Thread(self))
           \/ (\E self \in { "Destroyer" }: Destroy(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(Thread(self)) /\ WF_vars(UpdateLockState(self))
        /\ \A self \in { "Destroyer" } : WF_vars(Destroy(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Property ==
    /\  FairLock!Spec
    /\  []TypeOk
    /\  FairLock!Property
    /\  []\A thread \in Threads :
            \/  ENABLED(Lock(thread))
            \/  ~ \E lock \in Locks : lock.Thread = thread
            \/  ENABLED(Thread(thread))
            \/  ENABLED(UpdateLockState(thread))
            \/  ENABLED(Terminating)

Alias ==
    [
        LockCount |-> LockCount,
        Queue |-> Queue,
        Pending |-> Pending,
        Locks |-> Locks,
        ResumeLock |-> ResumeLock,
        LockState |-> LockState,
        \* Destroyed |-> Destroyed,
        pc |-> pc,
        stack |-> stack,

        \* Threads |-> [
        \*     thread \in Threads |-> [
        \*         LockEnabled |-> ENABLED(Lock(thread)),
        \*         Unlock_ReadEnabled |-> ENABLED(Unlock_Read(thread)),
        \*         Unlock_WriteEnabled |-> ENABLED(Unlock_Write(thread)),
        \*         WriteLockAcquired |-> WriteLock(thread) \in Locks,
        \*         ReadLockAcquired |-> ReadLock(thread) \in Locks,
        \*         EnqueueLock |-> ENABLED(EnqueueLock(thread)),
        \*         ThreadEnable |-> ENABLED(Thread(thread)),
        \*         UpdateLockState |-> ENABLED(UpdateLockState(thread))
        \*     ]
        \* ],
        lockToUnlock |-> lockToUnlock,
        lockToEnqueue |-> lockToEnqueue,
        locksToResume |-> locksToResume,
        nextLockState |-> nextLockState,
        previousLockState |-> previousLockState,
        unservedPendingDecrements |-> unservedPendingDecrements,
        HasPendingDecrements |-> HasPendingDecrements,
        PendingLockDecrementCount |-> PendingLockDecrementCount
        \* FairLock |-> FairLock!Alias,
        \* AbstractLocks |-> AbstractLocks,
        \* TypeOk |-> TypeOk
    ]
==== 
