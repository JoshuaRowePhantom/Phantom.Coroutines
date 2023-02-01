---- MODULE ReaderWriterLock ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    ReaderLockCount,
    Queue,
    Locks,
    Destroyed,
    locksToResume,
    lockToUnlock

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
    /\  ReaderLockCount \in -1..Cardinality(Threads)
    /\  Queue \in FairLock!QueueType
    /\  Locks \in SUBSET LockType
    /\  Destroyed \in BOOLEAN

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

CanDestroy ==
    /\  \A thread \in Threads :
        /\  lockToUnlock[thread] = { }
    /\  AbstractLocks = { }
    /\  Queue = << >>

(* --algorithm ReaderWriterLock

variables
    \* -1 = locked for write
    \* 0 = unlocked
    \* > 0 = # of readers
    ReaderLockCount = 0,
    Queue = << >>,
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
    lockToUnlock = { }
)
    variable locksToResume = << >>
begin
ResumeWaiters_CheckQueue:
    either
        assert ~Destroyed;
        await Queue = << >> \/ ReaderLockCount < 0;
        lockToUnlock := { };
        goto ResumeLocks;
    
    or
        assert ~Destroyed;
        await Queue # << >>;
        await ReaderLockCount > 0;
        await Queue[1].Type = "Write";
        lockToUnlock := { };
        goto ResumeLocks;
    
    or
        assert ~Destroyed;
        await Queue # << >>;
        await ReaderLockCount >= 0;
        lockToUnlock := { };
        with 
            index \in 1..Len(Queue) do

            locksToResume := SubSeq(Queue, 1, index);
            await 
                /\  \A otherIndex \in 1..Len(locksToResume) :
                    \/  /\  locksToResume[otherIndex].Type = "Read"
                        /\  index < Len(Queue) => Queue[index + 1].Type = "Write"
                    \/  /\  index = 1
                        /\  locksToResume[1].Type = "Write"
                        /\  ReaderLockCount = 0;

            Queue := SubSeq(Queue, index + 1, Len(Queue));
            ReaderLockCount := IF locksToResume[1].Type = "Write" THEN -1 ELSE Len(locksToResume);
            Locks := { }
        end with;
        
ResumeLocks:
        while locksToResume # << >> do
            Locks := Locks \union { Head(locksToResume) };
            locksToResume := Tail(locksToResume);
        end while;
        return;
    end either;
end procedure;

fair process Thread \in Threads
begin
Lock:
    either 
        await Destroyed;
    or
    await ~Destroyed;
    either
        \* Become a reader fast.
        await ReaderLockCount >= 0 /\ Queue = << >>;
        ReaderLockCount := ReaderLockCount + 1;
        AddLock(ReadLock(self));
        goto Unlock_Read;
    or
        \* Become a writer fast.
        await ReaderLockCount = 0 /\ Queue = << >>;
        ReaderLockCount := -1;
        AddLock(WriteLock(self));
        goto Unlock_Write;
    or
        \* Enqueue for read
        await ReaderLockCount = -1 \/ Queue # << >>;
        Queue := Queue \o << ReadLock(self) >>;

Unlock_Read:
        assert ~Destroyed;
        await ReadLock(self) \in Locks;
        Locks := Locks \ { ReadLock(self) };
        ReaderLockCount := ReaderLockCount - 1;
        if ReaderLockCount = 0 then
            call ResumeWaiters({ ReadLock(self) });
            goto Lock;
        else
            goto Lock;
        end if;

    or
        \* Enqueue for write
        await ReaderLockCount # 0 \/ Queue # << >>;
        Queue := Queue \o << WriteLock(self) >>;

Unlock_Write:
        assert ~Destroyed;
        await WriteLock(self) \in Locks;
        ReaderLockCount := 0;
        Locks := Locks \ { WriteLock(self) };
        call ResumeWaiters({ WriteLock(self) });
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
\* BEGIN TRANSLATION (chksum(pcal) = "656e1765" /\ chksum(tla) = "2b2452b8")
VARIABLES ReaderLockCount, Queue, Locks, Destroyed, pc, stack, lockToUnlock, 
          locksToResume

vars == << ReaderLockCount, Queue, Locks, Destroyed, pc, stack, lockToUnlock, 
           locksToResume >>

ProcSet == (Threads) \cup ({ "Destroyer" })

Init == (* Global variables *)
        /\ ReaderLockCount = 0
        /\ Queue = << >>
        /\ Locks = { }
        /\ Destroyed = FALSE
        (* Procedure ResumeWaiters *)
        /\ lockToUnlock = [ self \in ProcSet |-> { }]
        /\ locksToResume = [ self \in ProcSet |-> << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Lock"
                                        [] self \in { "Destroyer" } -> "DestroyIfIdle"]

ResumeWaiters_CheckQueue(self) == /\ pc[self] = "ResumeWaiters_CheckQueue"
                                  /\ \/ /\ Assert(~Destroyed, 
                                                  "Failure of assertion at line 85, column 9.")
                                        /\ Queue = << >> \/ ReaderLockCount < 0
                                        /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = { }]
                                        /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                        /\ UNCHANGED <<ReaderLockCount, Queue, Locks, locksToResume>>
                                     \/ /\ Assert(~Destroyed, 
                                                  "Failure of assertion at line 91, column 9.")
                                        /\ Queue # << >>
                                        /\ ReaderLockCount > 0
                                        /\ Queue[1].Type = "Write"
                                        /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = { }]
                                        /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                        /\ UNCHANGED <<ReaderLockCount, Queue, Locks, locksToResume>>
                                     \/ /\ Assert(~Destroyed, 
                                                  "Failure of assertion at line 99, column 9.")
                                        /\ Queue # << >>
                                        /\ ReaderLockCount >= 0
                                        /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = { }]
                                        /\ \E index \in 1..Len(Queue):
                                             /\ locksToResume' = [locksToResume EXCEPT ![self] = SubSeq(Queue, 1, index)]
                                             /\ /\  \A otherIndex \in 1..Len(locksToResume'[self]) :
                                                    \/  /\  locksToResume'[self][otherIndex].Type = "Read"
                                                        /\  index < Len(Queue) => Queue[index + 1].Type = "Write"
                                                    \/  /\  index = 1
                                                        /\  locksToResume'[self][1].Type = "Write"
                                                        /\  ReaderLockCount = 0
                                             /\ Queue' = SubSeq(Queue, index + 1, Len(Queue))
                                             /\ ReaderLockCount' = (IF locksToResume'[self][1].Type = "Write" THEN -1 ELSE Len(locksToResume'[self]))
                                             /\ Locks' = { }
                                        /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                  /\ UNCHANGED << Destroyed, stack >>

ResumeLocks(self) == /\ pc[self] = "ResumeLocks"
                     /\ IF locksToResume[self] # << >>
                           THEN /\ Locks' = (Locks \union { Head(locksToResume[self]) })
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Tail(locksToResume[self])]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeLocks"]
                                /\ UNCHANGED << stack, lockToUnlock >>
                           ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = Head(stack[self]).locksToResume]
                                /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = Head(stack[self]).lockToUnlock]
                                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                /\ Locks' = Locks
                     /\ UNCHANGED << ReaderLockCount, Queue, Destroyed >>

ResumeWaiters(self) == ResumeWaiters_CheckQueue(self) \/ ResumeLocks(self)

Lock(self) == /\ pc[self] = "Lock"
              /\ \/ /\ Destroyed
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED <<ReaderLockCount, Queue, Locks>>
                 \/ /\ ~Destroyed
                    /\ \/ /\ ReaderLockCount >= 0 /\ Queue = << >>
                          /\ ReaderLockCount' = ReaderLockCount + 1
                          /\ Locks' = (Locks \union { (ReadLock(self)) })
                          /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                          /\ Queue' = Queue
                       \/ /\ ReaderLockCount = 0 /\ Queue = << >>
                          /\ ReaderLockCount' = -1
                          /\ Locks' = (Locks \union { (WriteLock(self)) })
                          /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                          /\ Queue' = Queue
                       \/ /\ ReaderLockCount = -1 \/ Queue # << >>
                          /\ Queue' = Queue \o << ReadLock(self) >>
                          /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                          /\ UNCHANGED <<ReaderLockCount, Locks>>
                       \/ /\ ReaderLockCount # 0 \/ Queue # << >>
                          /\ Queue' = Queue \o << WriteLock(self) >>
                          /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                          /\ UNCHANGED <<ReaderLockCount, Locks>>
              /\ UNCHANGED << Destroyed, stack, lockToUnlock, locksToResume >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 154, column 9.")
                     /\ ReadLock(self) \in Locks
                     /\ Locks' = Locks \ { ReadLock(self) }
                     /\ ReaderLockCount' = ReaderLockCount - 1
                     /\ IF ReaderLockCount' = 0
                           THEN /\ /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = { ReadLock(self) }]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                            pc        |->  "Lock",
                                                                            locksToResume |->  locksToResume[self],
                                                                            lockToUnlock |->  lockToUnlock[self] ] >>
                                                                        \o stack[self]]
                                /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                                /\ pc' = [pc EXCEPT ![self] = "ResumeWaiters_CheckQueue"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Lock"]
                                /\ UNCHANGED << stack, lockToUnlock, 
                                                locksToResume >>
                     /\ UNCHANGED << Queue, Destroyed >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ Assert(~Destroyed, 
                                "Failure of assertion at line 171, column 9.")
                      /\ WriteLock(self) \in Locks
                      /\ ReaderLockCount' = 0
                      /\ Locks' = Locks \ { WriteLock(self) }
                      /\ /\ lockToUnlock' = [lockToUnlock EXCEPT ![self] = { WriteLock(self) }]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                  pc        |->  "Lock",
                                                                  locksToResume |->  locksToResume[self],
                                                                  lockToUnlock |->  lockToUnlock[self] ] >>
                                                              \o stack[self]]
                      /\ locksToResume' = [locksToResume EXCEPT ![self] = << >>]
                      /\ pc' = [pc EXCEPT ![self] = "ResumeWaiters_CheckQueue"]
                      /\ UNCHANGED << Queue, Destroyed >>

Thread(self) == Lock(self) \/ Unlock_Read(self) \/ Unlock_Write(self)

DestroyIfIdle(self) == /\ pc[self] = "DestroyIfIdle"
                       /\ CanDestroy
                       /\ Destroyed' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << ReaderLockCount, Queue, Locks, stack, 
                                       lockToUnlock, locksToResume >>

Destroy(self) == DestroyIfIdle(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: ResumeWaiters(self))
           \/ (\E self \in Threads: Thread(self))
           \/ (\E self \in { "Destroyer" }: Destroy(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(Thread(self)) /\ WF_vars(ResumeWaiters(self))
        /\ \A self \in { "Destroyer" } : WF_vars(Destroy(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Property ==
    /\  FairLock!Spec
    /\  []TypeOk
    /\  FairLock!Property
    /\  []\A thread \in Threads :
            /\  pc[thread] = "ResumeWaiters_CheckQueue" => ENABLED(ResumeWaiters_CheckQueue(thread))
            /\  pc[thread] = "Lock" => ENABLED(Lock(thread))

Alias ==
    [
        ReaderLockCount |-> ReaderLockCount,
        Queue |-> Queue,
        Locks |-> Locks,
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
                ResumeWaitersEnabled |-> ENABLED(ResumeWaiters_CheckQueue(thread))
            ]
        ],
        locksToResume |-> locksToResume,
        FairLock |-> FairLock!Alias,
        AbstractLocks |-> AbstractLocks
    ]
==== 
