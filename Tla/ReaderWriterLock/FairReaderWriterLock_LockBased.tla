---- MODULE FairReaderWriterLock_LockBased ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    ReaderLockCount,
    Queue,
    HasPending,
    Pending,
    Resuming,
    pending,
    Locks,
    Destroyed,
    locksToResume,
    lockToUnlock,
    lockToAcquire

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
    Pending 
    \o 
        (
            IF \E thread \in Threads : pending[thread] # << >> 
            THEN pending[CHOOSE thread \in Threads : pending[thread] # << >>]
            ELSE << >>
        )
    \o
        Queue

FairLock == 
    INSTANCE FairReaderWriterLock
    WITH 
    Locks <- AbstractLocks,
    Queue <- AbstractQueue

LockType == FairLock!LockType

AllThreads == Threads \union { "Destroyer" }

TypeOk ==
    /\  ReaderLockCount \in -1..Cardinality(Threads)
    /\  Queue \in FairLock!QueueType
    /\  Pending \in FairLock!QueueType
    /\  HasPending \in BOOLEAN
    /\  Resuming \in BOOLEAN
    /\  Locks \in SUBSET LockType
    /\  Destroyed \in BOOLEAN

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

CanDestroy ==
    /\  \A thread \in Threads :
        /\  lockToUnlock[thread] = << >>
    /\  \A thread \in Threads :
        /\  lockToAcquire[thread] = << >>
    /\  AbstractLocks = { }
    /\  Queue = << >>

(* --algorithm FairReaderWriterLock_LockBased

variables
    \* These three variables can be read \ written atomically.
    \* -1 = locked for write
    \* 0 = unlocked
    \* > 0 = # of readers
    ReaderLockCount = 0,
    Queue = << >>,
    HasPending = FALSE,
    Resuming = FALSE,

    Pending = << >>,
    Locks = { },
    Destroyed = FALSE;

macro AddLock(lock)
begin
    Locks := Locks \union { lock }
end macro;

macro Unlock(lock)
begin
    Locks := Locks \ { lock }
end macro;

macro AddWaiter(lock)
begin
    Queue :=  Queue \o << lock >>
end macro;

procedure ResumeWaiters(
    readerCountChange = 0,
    lockToUnlock = << >>
) variable 
    locksToResume = << >>,
    pending = << >>,
    readerCount = 0
begin
ResumeWaiters_CheckQueue:
    assert ~Destroyed;
    ReaderLockCount := ReaderLockCount + readerCountChange;
    readerCountChange := 0;

    if (Queue = << >> /\ ~HasPending) \/ (ReaderLockCount - readerCountChange) < 0 then
        goto ResumeLocks;
    elsif Resuming then
        goto ResumeLocks;
    else
        assert ~Destroyed;

        Queue := << >>
        ||
        pending := Queue
        ||
        HasPending := HasPending \/ Queue # << >>
        ||
        readerCount := ReaderLockCount
        ||
        Resuming := TRUE;

AppendToPending:
        while pending # << >> do
            assert ~Destroyed;
            Pending := Pending \o << Head(pending) >>;
            pending := Tail(pending);
        end while;

CollectAwaiters:
        while
            /\  Pending # << >>
            /\  \/  /\  readerCount >= 0
                    /\  Pending[1].Type = "Read"
                    /\  \/  /\  locksToResume # << >> 
                            /\  locksToResume[1].Type = "Read" 
                        \/  /\  locksToResume = << >>
            
                \/  /\  readerCount = 0
                    /\  Pending[1].Type = "Write"
                    /\  locksToResume = << >>

            do
            assert ~Destroyed;
            locksToResume := locksToResume \o << Head(Pending) >>;
            Pending := Tail(Pending);
        end while;
        
UpdateLockState:
        assert ~Destroyed;
        if Queue # << >> \/ ReaderLockCount # readerCount then
            pending := Queue;
            Queue := << >>;
            HasPending := pending # << >>;
            readerCount := ReaderLockCount;
            goto AppendToPending;
        elsif locksToResume # << >> then
            Resuming := FALSE;
            HasPending := Pending # << >>;
            if locksToResume[1].Type = "Write" then
                ReaderLockCount := -1;
            else
                ReaderLockCount := ReaderLockCount + Len(locksToResume);
            end if;
        else
            HasPending := Pending # << >>;
            Resuming := FALSE;
        end if;

ResumeLocks:
        while locksToResume # << >> do
            Locks := Locks \union { Head(locksToResume) };
            locksToResume := Tail(locksToResume);
        end while;
        return;
    end if;
end procedure;

procedure Lock(
    lockToAcquire = << >>
)
begin
AcquireOrEnqueue:
    assert ~Destroyed;
    if  /\  ~Resuming 
        /\  ReaderLockCount >= 0 
        /\  Queue = << >> 
        /\  ~HasPending 
        /\  lockToAcquire = ReadLock(self) 
        then
        \* Become a reader fast.
        ReaderLockCount := ReaderLockCount + 1;
        AddLock(lockToAcquire);
        goto Unlock_Read;
    elsif   
        /\  ~Resuming 
        /\  ReaderLockCount = 0 
        /\  Queue = << >> 
        /\  ~HasPending 
        /\  lockToAcquire = WriteLock(self) 
        then
        \* Become a writer fast.
        ReaderLockCount := -1;
        AddLock(lockToAcquire);
        goto Unlock_Write;
    elsif lockToAcquire = ReadLock(self) then
        \* Enqueue for read
        Queue := Queue \o << lockToAcquire >>;

Unlock_Read:
        assert ~Destroyed;
        await lockToAcquire \in Locks;
        Locks := Locks \ { lockToAcquire };
        call ResumeWaiters(-1, << lockToAcquire >>);

    else
        assert lockToAcquire = WriteLock(self);
        Queue := Queue \o << lockToAcquire >>;

Unlock_Write:
        assert ~Destroyed;
        await lockToAcquire \in Locks;
        Locks := Locks \ { lockToAcquire};
        call ResumeWaiters(1, << lockToAcquire >>);
    end if;

Lock_Done:
    lockToAcquire := << >>;
Lock_Return:
    return;
end procedure;

fair process Thread \in Threads
begin
Loop:
    while ~Destroyed do
        with proposal \in { ReadLock(self), WriteLock(self) } do
            call Lock(proposal);
        end with;
    end while;
end process;

fair process Destroy \in { "Destroyer" }
begin
DestroyIfIdle:
    await CanDestroy;
    Destroyed := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "158471d8" /\ chksum(tla) = "a956003a")
VARIABLES ReaderLockCount, Queue, HasPending, Resuming, Pending, Locks, 
          Destroyed, pc, stack, readerCountChange, lockToUnlock, 
          locksToResume, pending, readerCount, lockToAcquire

vars == << ReaderLockCount, Queue, HasPending, Resuming, Pending, Locks, 
           Destroyed, pc, stack, readerCountChange, lockToUnlock, 
           locksToResume, pending, readerCount, lockToAcquire >>

ProcSet == (Threads) \cup ({ "Destroyer" })

Init == (* Global variables *)
        /\ ReaderLockCount = 0
        /\ Queue = << >>
        /\ HasPending = FALSE
        /\ Resuming = FALSE
        /\ Pending = << >>
        /\ Locks = { }
        /\ Destroyed = FALSE
        (* Procedure ResumeWaiters *)
        /\ readerCountChange = [ self \in ProcSet |-> 0]
        /\ lockToUnlock = [ self \in ProcSet |-> << >>]
        /\ locksToResume = [ self \in ProcSet |-> << >>]
        /\ pending = [ self \in ProcSet |-> << >>]
        /\ readerCount = [ self \in ProcSet |-> 0]
        (* Procedure Lock *)
        /\ lockToAcquire = [ self \in ProcSet |-> << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Loop"
                                        [] self \in { "Destroyer" } -> "DestroyIfIdle"]

ResumeWaiters_CheckQueue(self) == /\ pc[self] = "ResumeWaiters_CheckQueue"
                                  /\ Assert(~Destroyed, 
                                            "Failure of assertion at line 114, column 5.")
                                  /\ ReaderLockCount' = ReaderLockCount + readerCountChange[self]
                                  /\ readerCountChange' = [readerCountChange EXCEPT ![self] = 0]
                                  /\ IF (Queue = << >> /\ ~HasPending) \/ (ReaderLockCount' - readerCountChange'[self]) < 0
                                        THEN /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                             /\ UNCHANGED << Queue, HasPending, 
                                                             Resuming, pending, 
                                                             readerCount >>
                                        ELSE /\ IF Resuming
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                                        /\ UNCHANGED << Queue, 
                                                                        HasPending, 
                                                                        Resuming, 
                                                                        pending, 
                                                                        readerCount >>
                                                   ELSE /\ Assert(~Destroyed, 
                                                                  "Failure of assertion at line 123, column 9.")
                                                        /\ /\ HasPending' = (HasPending \/ Queue # << >>)
                                                           /\ Queue' = << >>
                                                           /\ Resuming' = TRUE
                                                           /\ pending' = [pending EXCEPT ![self] = Queue]
                                                           /\ readerCount' = [readerCount EXCEPT ![self] = ReaderLockCount']
                                                        /\ pc' = [pc EXCEPT ![self] = "AppendToPending"]
                                  /\ UNCHANGED << Pending, Locks, Destroyed, 
                                                  stack, lockToUnlock, 
                                                  locksToResume, lockToAcquire >>

AppendToPending(self) == /\ pc[self] = "AppendToPending"
                         /\ IF pending[self] # << >>
                               THEN /\ Assert(~Destroyed, 
                                              "Failure of assertion at line 137, column 13.")
                                    /\ Pending' = Pending \o << Head(pending[self]) >>
                                    /\ pending' = [pending EXCEPT ![self] = Tail(pending[self])]
                                    /\ pc' = [pc EXCEPT ![self] = "AppendToPending"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "CollectAwaiters"]
                                    /\ UNCHANGED << Pending, pending >>
                         /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                         Resuming, Locks, Destroyed, stack, 
                                         readerCountChange, lockToUnlock, 
                                         locksToResume, readerCount, 
                                         lockToAcquire >>

CollectAwaiters(self) == /\ pc[self] = "CollectAwaiters"
                         /\ IF /\  Pending # << >>
                               /\  \/  /\  readerCount[self] >= 0
                                       /\  Pending[1].Type = "Read"
                                       /\  \/  /\  locksToResume[self] # << >>
                                               /\  locksToResume[self][1].Type = "Read"
                                           \/  /\  locksToResume[self] = << >>
                               
                                   \/  /\  readerCount[self] = 0
                                       /\  Pending[1].Type = "Write"
                                       /\  locksToResume[self] = << >>
                               THEN /\ Assert(~Destroyed, 
                                              "Failure of assertion at line 156, column 13.")
                                    /\ locksToResume' = [locksToResume EXCEPT ![self] = locksToResume[self] \o << Head(Pending) >>]
                                    /\ Pending' = Tail(Pending)
                                    /\ pc' = [pc EXCEPT ![self] = "CollectAwaiters"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "UpdateLockState"]
                                    /\ UNCHANGED << Pending, locksToResume >>
                         /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                         Resuming, Locks, Destroyed, stack, 
                                         readerCountChange, lockToUnlock, 
                                         pending, readerCount, lockToAcquire >>

UpdateLockState(self) == /\ pc[self] = "UpdateLockState"
                         /\ Assert(~Destroyed, 
                                   "Failure of assertion at line 162, column 9.")
                         /\ IF Queue # << >> \/ ReaderLockCount # readerCount[self]
                               THEN /\ pending' = [pending EXCEPT ![self] = Queue]
                                    /\ Queue' = << >>
                                    /\ HasPending' = (pending'[self] # << >>)
                                    /\ readerCount' = [readerCount EXCEPT ![self] = ReaderLockCount]
                                    /\ pc' = [pc EXCEPT ![self] = "AppendToPending"]
                                    /\ UNCHANGED << ReaderLockCount, Resuming >>
                               ELSE /\ IF locksToResume[self] # << >>
                                          THEN /\ Resuming' = FALSE
                                               /\ HasPending' = (Pending # << >>)
                                               /\ IF locksToResume[self][1].Type = "Write"
                                                     THEN /\ ReaderLockCount' = -1
                                                     ELSE /\ ReaderLockCount' = ReaderLockCount + Len(locksToResume[self])
                                          ELSE /\ HasPending' = (Pending # << >>)
                                               /\ Resuming' = FALSE
                                               /\ UNCHANGED ReaderLockCount
                                    /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                    /\ UNCHANGED << Queue, pending, 
                                                    readerCount >>
                         /\ UNCHANGED << Pending, Locks, Destroyed, stack, 
                                         readerCountChange, lockToUnlock, 
                                         locksToResume, lockToAcquire >>

ResumeLocks(self) == /\ pc[self] = "ResumeLocks"
                     /\ IF locksToResume[self] # << >>
                           THEN /\ Locks' = (Locks \union { Head(locksToResume[self]) })
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Tail(locksToResume[self])]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED << stack, readerCountChange, 
                                                lockToUnlock, pending, 
                                                readerCount >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Head(stack[self]).locksToResume]
                                /\ pending' = [pending EXCEPT ![self] = Head(stack[self]).pending]
                                /\ readerCount' = [readerCount EXCEPT ![self] = Head(stack[self]).readerCount]
                                /\ readerCountChange' = [readerCountChange EXCEPT ![self] = Head(stack[self]).readerCountChange]
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = Head(stack[self]).lockToUnlock]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ Locks' = Locks
                     /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                     Resuming, Pending, Destroyed, 
                                     lockToAcquire >>

ResumeWaiters(self) == ResumeWaiters_CheckQueue(self)
                          \/ AppendToPending(self) \/ CollectAwaiters(self)
                          \/ UpdateLockState(self) \/ ResumeLocks(self)

AcquireOrEnqueue(self) == /\ pc[self] = "AcquireOrEnqueue"
                          /\ Assert(~Destroyed, 
                                    "Failure of assertion at line 196, column 5.")
                          /\ IF /\  ~Resuming
                                /\  ReaderLockCount >= 0
                                /\  Queue = << >>
                                /\  ~HasPending
                                /\  lockToAcquire[self] = ReadLock(self)
                                THEN /\ ReaderLockCount' = ReaderLockCount + 1
                                     /\ Locks' = (Locks \union { lockToAcquire[self] })
                                     /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                                     /\ Queue' = Queue
                                ELSE /\ IF /\  ~Resuming
                                           /\  ReaderLockCount = 0
                                           /\  Queue = << >>
                                           /\  ~HasPending
                                           /\  lockToAcquire[self] = WriteLock(self)
                                           THEN /\ ReaderLockCount' = -1
                                                /\ Locks' = (Locks \union { lockToAcquire[self] })
                                                /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                                                /\ Queue' = Queue
                                           ELSE /\ IF lockToAcquire[self] = ReadLock(self)
                                                      THEN /\ Queue' = Queue \o << lockToAcquire[self] >>
                                                           /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                                                      ELSE /\ Assert(lockToAcquire[self] = WriteLock(self), 
                                                                     "Failure of assertion at line 229, column 9.")
                                                           /\ Queue' = Queue \o << lockToAcquire[self] >>
                                                           /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                                                /\ UNCHANGED << ReaderLockCount, 
                                                                Locks >>
                          /\ UNCHANGED << HasPending, Resuming, Pending, 
                                          Destroyed, stack, readerCountChange, 
                                          lockToUnlock, locksToResume, pending, 
                                          readerCount, lockToAcquire >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 223, column 9.")
                     /\ lockToAcquire[self] \in Locks
                     /\ Locks' = Locks \ { lockToAcquire[self] }
                     /\ /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << lockToAcquire[self] >>]
                        /\ readerCountChange' = [readerCountChange EXCEPT ![self] = -1]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                 pc        |->  "Lock_Done",
                                                                 locksToResume |->  locksToResume[self],
                                                                 pending   |->  pending[self],
                                                                 readerCount |->  readerCount[self],
                                                                 readerCountChange |->  readerCountChange[self],
                                                                 lockToUnlock |->  lockToUnlock[self] ] >>
                                                             \o stack[self]]
                     /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                     /\ pending' = [pending EXCEPT ![self] = << >>]
                     /\ readerCount' = [readerCount EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "ResumeWaiters_CheckQueue"]
                     /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                     Resuming, Pending, Destroyed, 
                                     lockToAcquire >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ Assert(~Destroyed, 
                                "Failure of assertion at line 233, column 9.")
                      /\ lockToAcquire[self] \in Locks
                      /\ Locks' = Locks \ { lockToAcquire[self]}
                      /\ /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = << lockToAcquire[self] >>]
                         /\ readerCountChange' = [readerCountChange EXCEPT ![self] = 1]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                  pc        |->  "Lock_Done",
                                                                  locksToResume |->  locksToResume[self],
                                                                  pending   |->  pending[self],
                                                                  readerCount |->  readerCount[self],
                                                                  readerCountChange |->  readerCountChange[self],
                                                                  lockToUnlock |->  lockToUnlock[self] ] >>
                                                              \o stack[self]]
                      /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                      /\ pending' = [pending EXCEPT ![self] = << >>]
                      /\ readerCount' = [readerCount EXCEPT ![self] = 0]
                      /\ pc' = [pc EXCEPT ![self] = "ResumeWaiters_CheckQueue"]
                      /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                      Resuming, Pending, Destroyed, 
                                      lockToAcquire >>

Lock_Done(self) == /\ pc[self] = "Lock_Done"
                   /\ lockToAcquire' = [lockToAcquire EXCEPT ![self] = << >>]
                   /\ pc' = [pc EXCEPT ![self] = "Lock_Return"]
                   /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                   Resuming, Pending, Locks, Destroyed, stack, 
                                   readerCountChange, lockToUnlock, 
                                   locksToResume, pending, readerCount >>

Lock_Return(self) == /\ pc[self] = "Lock_Return"
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ lockToAcquire' = [lockToAcquire EXCEPT ![self] = Head(stack[self]).lockToAcquire]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                     Resuming, Pending, Locks, Destroyed, 
                                     readerCountChange, lockToUnlock, 
                                     locksToResume, pending, readerCount >>

Lock(self) == AcquireOrEnqueue(self) \/ Unlock_Read(self)
                 \/ Unlock_Write(self) \/ Lock_Done(self)
                 \/ Lock_Return(self)

Loop(self) == /\ pc[self] = "Loop"
              /\ IF ~Destroyed
                    THEN /\ \E proposal \in { ReadLock(self), WriteLock(self) }:
                              /\ /\ lockToAcquire' = [lockToAcquire EXCEPT ![self] = proposal]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Lock",
                                                                          pc        |->  "Loop",
                                                                          lockToAcquire |->  lockToAcquire[self] ] >>
                                                                      \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "AcquireOrEnqueue"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << stack, lockToAcquire >>
              /\ UNCHANGED << ReaderLockCount, Queue, HasPending, Resuming, 
                              Pending, Locks, Destroyed, readerCountChange, 
                              lockToUnlock, locksToResume, pending, 
                              readerCount >>

Thread(self) == Loop(self)

DestroyIfIdle(self) == /\ pc[self] = "DestroyIfIdle"
                       /\ CanDestroy
                       /\ Destroyed' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << ReaderLockCount, Queue, HasPending, 
                                       Resuming, Pending, Locks, stack, 
                                       readerCountChange, lockToUnlock, 
                                       locksToResume, pending, readerCount, 
                                       lockToAcquire >>

Destroy(self) == DestroyIfIdle(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: ResumeWaiters(self) \/ Lock(self))
           \/ (\E self \in Threads: Thread(self))
           \/ (\E self \in { "Destroyer" }: Destroy(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : /\ WF_vars(Thread(self))
                                 /\ WF_vars(Lock(self))
                                 /\ WF_vars(ResumeWaiters(self))
        /\ \A self \in { "Destroyer" } : WF_vars(Destroy(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Property ==
    /\  FairLock!Spec
    /\  []TypeOk
    /\  FairLock!Property
    /\  []\A thread \in Threads :
            /\  pc[thread] \notin {"Unlock_Read", "Unlock_Write", "Done"} => ENABLED(
                    \/  Thread(thread) 
                    \/  ResumeWaiters(thread) 
                    \/  Lock(thread)
                )

Alias ==
    [
        ReaderLockCount |-> ReaderLockCount,
        Queue |-> Queue,
        Pending |-> Pending,
        pending |-> pending,
        HasPending |-> HasPending,
        Locks |-> Locks,
        Destroyed |-> Destroyed,
        Resuming |-> Resuming,
        pc |-> pc,
        stack |-> stack,
        Threads |-> [
            thread \in Threads |-> [
                LockEnabled |-> ENABLED(Lock(thread)),
                Unlock_ReadEnabled |-> ENABLED(Unlock_Read(thread)),
                Unlock_WriteEnabled |-> ENABLED(Unlock_Write(thread)),
                WriteLockAcquired |-> WriteLock(thread) \in Locks,
                ReadLockAcquired |-> ReadLock(thread) \in Locks,
                ResumeWaitersEnabled |-> ENABLED(ResumeWaiters_CheckQueue(thread))
            ]
        ],
        readerCountChange |-> readerCountChange,
        readerCount |-> readerCount,
        locksToResume |-> locksToResume,
        FairLock |-> FairLock!Alias,
        AbstractLocks |-> AbstractLocks
    ]
==== 
