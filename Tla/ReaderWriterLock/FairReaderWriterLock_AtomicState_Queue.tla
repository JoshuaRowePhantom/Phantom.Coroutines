---- MODULE FairReaderWriterLock_AtomicState_Queue ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    LockCount,

    \* These three variables can be atomically read-modify-written.
    ResumeLock,
    LockState,
    Queue,

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

FairLock == 
    INSTANCE FairReaderWriterLock
    WITH 
    Locks <- AbstractLocks

LockType == FairLock!LockType

AllThreads == Threads \union { "Destroyer" }

TypeOk ==
    /\  LockCount \in -1..Cardinality(Threads)
    /\  ResumeLock \in { "Unlocked", "Resuming", "ModifiedWhileResuming" }
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

(* --algorithm FairReaderWriterLock_AtomicState_Queue

variables
    \* -1 = locked for write
    \* 0 = unlocked
    \* > 0 = # of readers
    LockCount = 0,
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

macro UnlockLastLock(lockToUnlock)
begin
    if lockToUnlock # << >> then
        if lockToUnlock.Type = "Read" then
            LockCount := LockCount - 1;
            lockToUnlock := << >>
        else
            assert lockToUnlock.Type = "Write";
            LockCount := 0;
            lockToUnlock := << >>
        end if
    end if;
end macro;

procedure UpdateLockState(
    lockToEnqueue = << >>,
    lockToUnlock = << >>
)
variable locksToResume = << >>
begin
EnqueueLock:
    assert ~Destroyed;
    assert Len(lockToEnqueue \o lockToUnlock) = 1;
    
    if  /\  lockToEnqueue # << >>
        /\  ResumeLock \in { "Resuming", "ModifiedWhileResuming" }
        then
        Queue := Queue \o lockToEnqueue;
        lockToEnqueue := << >>;
        ResumeLock := "ModifiedWhileResuming";
        lockToUnlock := << >>;
        goto ResumeLocks;
    elsif 
        \/  LockState = "Write" /\ lockToEnqueue # << >>
        \/  LockState = "Read" /\ lockToEnqueue # << >> /\ lockToEnqueue[1].Type = "Write" then
        Queue := Queue \o lockToEnqueue;
        lockToUnlock := << >>;
        goto ResumeLocks;
    else
        ResumeLock := "Resuming";
        \* This set to Pending is not atomic, but we don't require atomicity for
        \* assignments to atomic. We atomically exchange the queue for empty,
        \* then non-atomically add the items in the queue to Pending.
        \* In a real implementation, we appended to queue by writing to the list head,
        \* and the assignment to Pending traverses the queue and reverses the Queue
        \* while appending to Pending.
        Pending := Pending \o Queue \o lockToEnqueue;
        Queue := << >>;
        goto CollectPendingLocks;
    end if;

CollectPendingLocks:
    assert ~Destroyed;
    with 
        allPendingLocks = locksToResume \o Pending,
        index \in 0..Len(allPendingLocks)
        do

        locksToResume := SubSeq(allPendingLocks, 1, index);
        Pending := SubSeq(Pending, index + 1, Len(Pending));

        await 
            /\  \A otherIndex \in 1..Len(locksToResume) :
                /\  LocksAreCompatible(locksToResume[1], locksToResume[otherIndex])
            /\  (index = 0 => 
                    \/  /\  allPendingLocks = << >>)
            /\  \/  lockToUnlock # << >>
                \/  index > 1 => LockState = "Read";
        
        if  /\  locksToResume = << >>
            /\  lockToUnlock # << >> then
            assert LockState # "Unlocked";
            LockCount := 0;
        end if;

    end with;

CheckResumeLock:
    assert ~Destroyed;
    lockToUnlock := << >>;
    if ResumeLock = "ModifiedWhileResuming" then
        Pending := Pending \o Queue;
        Queue := << >>;
        ResumeLock := "Resuming";
        goto CollectPendingLocks;
    elsif locksToResume # << >> then
        LockState := locksToResume[1].Type;
        ResumeLock := "Unlocked";
    else
        LockState := "Unlocked";
        ResumeLock := "Unlocked";
    end if;

ResumeLocks:
    while locksToResume # << >> do
        if Head(locksToResume).Type = "Write" then
            LockCount := -1;
        elsif   /\  lockToUnlock # << >> 
                /\  lockToUnlock.Type = "Write" 
                /\  Head(locksToResume).Type = "Read" 
                /\  LockCount < 1 then
            LockCount := 1
        else
            LockCount := LockCount + 1;
        end if;

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
        LockCount := LockCount - 1;
        if LockCount = 0 then
            call UpdateLockState(
                << >>,
                << ReadLock(self) >>);
            goto Lock;
        end if;

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
\* BEGIN TRANSLATION (chksum(pcal) = "ab213cbc" /\ chksum(tla) = "dbaec05")
VARIABLES LockCount, ResumeLock, LockState, Queue, Pending, Locks, Destroyed, 
          pc, stack, lockToEnqueue, lockToUnlock, locksToResume

vars == << LockCount, ResumeLock, LockState, Queue, Pending, Locks, Destroyed, 
           pc, stack, lockToEnqueue, lockToUnlock, locksToResume >>

ProcSet == (Threads) \cup ({ "Destroyer" })

Init == (* Global variables *)
        /\ LockCount = 0
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
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Lock"
                                        [] self \in { "Destroyer" } -> "DestroyIfIdle"]

EnqueueLock(self) == /\ pc[self] = "EnqueueLock"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 118, column 5.")
                     /\ Assert(Len(lockToEnqueue[self] \o lockToUnlock[self]) = 1, 
                               "Failure of assertion at line 119, column 5.")
                     /\ IF /\  lockToEnqueue[self] # << >>
                           /\  ResumeLock \in { "Resuming", "ModifiedWhileResuming" }
                           THEN /\ Queue' = Queue \o lockToEnqueue[self]
                                /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                                /\ ResumeLock' = "ModifiedWhileResuming"
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED Pending
                           ELSE /\ IF \/  LockState = "Write" /\ lockToEnqueue[self] # << >>
                                      \/  LockState = "Read" /\ lockToEnqueue[self] # << >> /\ lockToEnqueue[self][1].Type = "Write"
                                      THEN /\ Queue' = Queue \o lockToEnqueue[self]
                                           /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                                           /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                           /\ UNCHANGED << ResumeLock, Pending >>
                                      ELSE /\ ResumeLock' = "Resuming"
                                           /\ Pending' = Pending \o Queue \o lockToEnqueue[self]
                                           /\ Queue' = << >>
                                           /\ pc' = [pc EXCEPT ![self] = "CollectPendingLocks"]
                                           /\ UNCHANGED lockToUnlock
                                /\ UNCHANGED lockToEnqueue
                     /\ UNCHANGED << LockCount, LockState, Locks, Destroyed, 
                                     stack, locksToResume >>

CollectPendingLocks(self) == /\ pc[self] = "CollectPendingLocks"
                             /\ Assert(~Destroyed, 
                                       "Failure of assertion at line 149, column 5.")
                             /\ LET allPendingLocks == locksToResume[self] \o Pending IN
                                  \E index \in 0..Len(allPendingLocks):
                                    /\ locksToResume' = [locksToResume EXCEPT ![self] = SubSeq(allPendingLocks, 1, index)]
                                    /\ Pending' = SubSeq(Pending, index + 1, Len(Pending))
                                    /\ /\  \A otherIndex \in 1..Len(locksToResume'[self]) :
                                           /\  LocksAreCompatible(locksToResume'[self][1], locksToResume'[self][otherIndex])
                                       /\  (index = 0 =>
                                               \/  /\  allPendingLocks = << >>)
                                       /\  \/  lockToUnlock[self] # << >>
                                           \/  index > 1 => LockState = "Read"
                                    /\ IF /\  locksToResume'[self] = << >>
                                          /\  lockToUnlock[self] # << >>
                                          THEN /\ Assert(LockState # "Unlocked", 
                                                         "Failure of assertion at line 168, column 13.")
                                               /\ LockCount' = 0
                                          ELSE /\ TRUE
                                               /\ UNCHANGED LockCount
                             /\ pc' = [pc EXCEPT ![self] = "CheckResumeLock"]
                             /\ UNCHANGED << ResumeLock, LockState, Queue, 
                                             Locks, Destroyed, stack, 
                                             lockToEnqueue, lockToUnlock >>

CheckResumeLock(self) == /\ pc[self] = "CheckResumeLock"
                         /\ Assert(~Destroyed, 
                                   "Failure of assertion at line 175, column 5.")
                         /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                         /\ IF ResumeLock = "ModifiedWhileResuming"
                               THEN /\ Pending' = Pending \o Queue
                                    /\ Queue' = << >>
                                    /\ ResumeLock' = "Resuming"
                                    /\ pc' = [pc EXCEPT ![self] = "CollectPendingLocks"]
                                    /\ UNCHANGED LockState
                               ELSE /\ IF locksToResume[self] # << >>
                                          THEN /\ LockState' = locksToResume[self][1].Type
                                               /\ ResumeLock' = "Unlocked"
                                          ELSE /\ LockState' = "Unlocked"
                                               /\ ResumeLock' = "Unlocked"
                                    /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                    /\ UNCHANGED << Queue, Pending >>
                         /\ UNCHANGED << LockCount, Locks, Destroyed, stack, 
                                         lockToEnqueue, locksToResume >>

ResumeLocks(self) == /\ pc[self] = "ResumeLocks"
                     /\ IF locksToResume[self] # << >>
                           THEN /\ IF Head(locksToResume[self]).Type = "Write"
                                      THEN /\ LockCount' = -1
                                      ELSE /\ IF /\  lockToUnlock[self] # << >>
                                                 /\  lockToUnlock[self].Type = "Write"
                                                 /\  Head(locksToResume[self]).Type = "Read"
                                                 /\  LockCount < 1
                                                 THEN /\ LockCount' = 1
                                                 ELSE /\ LockCount' = LockCount + 1
                                /\ /\ Locks' = (Locks \union { Head(locksToResume[self]) })
                                   /\ locksToResume' = [locksToResume EXCEPT ![self] = Tail(locksToResume[self])]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED << stack, lockToEnqueue, 
                                                lockToUnlock >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Head(stack[self]).locksToResume]
                                /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = Head(stack[self]).lockToEnqueue]
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = Head(stack[self]).lockToUnlock]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ UNCHANGED << LockCount, Locks >>
                     /\ UNCHANGED << ResumeLock, LockState, Queue, Pending, 
                                     Destroyed >>

UpdateLockState(self) == EnqueueLock(self) \/ CollectPendingLocks(self)
                            \/ CheckResumeLock(self) \/ ResumeLocks(self)

Lock(self) == /\ pc[self] = "Lock"
              /\ \/ /\ Destroyed
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED <<stack, lockToEnqueue, lockToUnlock, locksToResume>>
                 \/ /\ ~Destroyed
                    /\ \/ /\ Assert(~Destroyed, 
                                    "Failure of assertion at line 219, column 9.")
                          /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << ReadLock(self) >>]
                             /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                      pc        |->  "Unlock_Read",
                                                                      locksToResume |->  locksToResume[self],
                                                                      lockToEnqueue |->  lockToEnqueue[self],
                                                                      lockToUnlock |->  lockToUnlock[self] ] >>
                                                                  \o stack[self]]
                          /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                          /\ pc' = [pc EXCEPT ![self] = "EnqueueLock"]
                       \/ /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << WriteLock(self) >>]
                             /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << >>]
                             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                      pc        |->  "Unlock_Write",
                                                                      locksToResume |->  locksToResume[self],
                                                                      lockToEnqueue |->  lockToEnqueue[self],
                                                                      lockToUnlock |->  lockToUnlock[self] ] >>
                                                                  \o stack[self]]
                          /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                          /\ pc' = [pc EXCEPT ![self] = "EnqueueLock"]
              /\ UNCHANGED << LockCount, ResumeLock, LockState, Queue, Pending, 
                              Locks, Destroyed >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 226, column 9.")
                     /\ ReadLock(self) \in Locks
                     /\ Locks' = Locks \ { ReadLock(self) }
                     /\ LockCount' = LockCount - 1
                     /\ IF LockCount' = 0
                           THEN /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                                   /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << ReadLock(self) >>]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                            pc        |->  "Lock",
                                                                            locksToResume |->  locksToResume[self],
                                                                            lockToEnqueue |->  lockToEnqueue[self],
                                                                            lockToUnlock |->  lockToUnlock[self] ] >>
                                                                        \o stack[self]]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                                /\ pc' = [pc EXCEPT ![self] = "EnqueueLock"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                /\ UNCHANGED << stack, lockToEnqueue, 
                                                lockToUnlock, locksToResume >>
                     /\ UNCHANGED << ResumeLock, LockState, Queue, Pending, 
                                     Destroyed >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ Assert(~Destroyed, 
                                "Failure of assertion at line 245, column 9.")
                      /\ WriteLock(self) \in Locks
                      /\ Locks' = Locks \ { WriteLock(self) }
                      /\ /\ lockToEnqueue' = [lockToEnqueue EXCEPT ![self] = << >>]
                         /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << WriteLock(self) >>]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UpdateLockState",
                                                                  pc        |->  "Lock",
                                                                  locksToResume |->  locksToResume[self],
                                                                  lockToEnqueue |->  lockToEnqueue[self],
                                                                  lockToUnlock |->  lockToUnlock[self] ] >>
                                                              \o stack[self]]
                      /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                      /\ pc' = [pc EXCEPT ![self] = "EnqueueLock"]
                      /\ UNCHANGED << LockCount, ResumeLock, LockState, Queue, 
                                      Pending, Destroyed >>

Thread(self) == Lock(self) \/ Unlock_Read(self) \/ Unlock_Write(self)

DestroyIfIdle(self) == /\ pc[self] = "DestroyIfIdle"
                       /\ CanDestroy
                       /\ Destroyed' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << LockCount, ResumeLock, LockState, Queue, 
                                       Pending, Locks, stack, lockToEnqueue, 
                                       lockToUnlock, locksToResume >>

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
        Destroyed |-> Destroyed,
        pc |-> pc,
        stack |-> stack,
        Threads |-> [
            thread \in Threads |-> [
                LockEnabled |-> ENABLED(Lock(thread)),
                Unlock_ReadEnabled |-> ENABLED(Unlock_Read(thread)),
                Unlock_WriteEnabled |-> ENABLED(Unlock_Write(thread)),
                WriteLockAcquired |-> WriteLock(thread) \in Locks,
                ReadLockAcquired |-> ReadLock(thread) \in Locks,
                EnqueueLock |-> ENABLED(EnqueueLock(thread)),
                ThreadEnable |-> ENABLED(Thread(thread)),
                UpdateLockState |-> ENABLED(UpdateLockState(thread))
            ]
        ],
        lockToUnlock |-> lockToUnlock,
        lockToEnqueue |-> lockToEnqueue,
        locksToResume |-> locksToResume,
        FairLock |-> FairLock!Alias,
        AbstractLocks |-> AbstractLocks
    ]
==== 
