---- MODULE ReaderWriterLock ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    State,
    Queue,
    Locks,
    Destroyed,
    queueEntry

AwaiterListType == Seq(Threads)

AbstractQueue == (
            IF 
                \E thread \in Threads :
                    /\  queueEntry[thread] # << >> 
                    /\  ~ \E index \in DOMAIN Queue : << Queue[index] >> = queueEntry[thread]
            THEN
                queueEntry[CHOOSE thread \in Threads : queueEntry[thread] # << >>]
            ELSE
                << >>
        ) \o Queue

FairLock == 
    INSTANCE FairReaderWriterLock
    WITH Queue <- AbstractQueue

LockType == FairLock!LockType

AllThreads == Threads \union { "Destroyer" }

TypeOk ==
    /\  State \in (-Cardinality(Threads) - 1)..(Cardinality(Threads) + 1)
    /\  Queue \in FairLock!QueueType
    /\  Locks \in SUBSET LockType
    /\  Destroyed \in BOOLEAN
    /\  queueEntry \in [ AllThreads -> { << >> } \union { << lock >> : lock \in LockType } ]

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

StateActionValue(oldState, unlock) ==
    LET
        isResumerLocked == oldState < 0
        oldReaderCount == IF oldState >= 2 THEN oldState - 1 ELSE IF oldState <= -2 THEN (-oldState) - 1 ELSE 0
        isWriteLocked == (oldState = 1)
    IN
        \* We were the writer, and we've become unlocked, so we should become the resumer.
        IF isWriteLocked /\ unlock THEN -1 
        \* The lock is write-locked and we're not the owner. There's nothing to resume.
        ELSE IF isWriteLocked THEN 1
        \* May go from reader count 1 to reader count 0 w/ resumer locked, old state = -2 new state = -1
        ELSE IF isResumerLocked /\ unlock THEN oldState + 1 
        \* We're not unlocked, and the resumer is locked. Let the existing resumer do its thing.
        ELSE IF isResumerLocked THEN oldState
        \* This was the last reader, and the resumer is not locked, so we should become the resumer.
        ELSE IF oldReaderCount = 1 /\ unlock THEN -1
        \* This was a reader, the resumer is not locked, but we're not unlocking the last reader,
        \* so there's nothing to resume.
        ELSE IF unlock THEN oldState - 1
        \* The caller doesn't want to unlock anything,
        \* but just wants to check if resuming is needed,
        \* which is necessary if the resumer is not locked.
        ELSE IF ~isResumerLocked /\ ~unlock /\ oldReaderCount = 0 THEN -1
        \* The caller doesn't want to unlock anything
        ELSE oldState
        
ResumeAction(oldState, newState) ==
    oldState >= 0 /\ newState < 0

StateAction(oldState, unlock) ==
    [
        NewState |-> StateActionValue(oldState, unlock),
        Resume |-> ResumeAction(oldState, StateActionValue(oldState, unlock))
    ]
(* --algorithm ReaderWriterLock

variables
    \* 0 = nothing is going on.
    \* 1 = locked for write
    \* >= 2 = locked for read
    \* -1 = locked for resuming waiters
    \* <= -2 = locked for resuming waiters while read lock held,
    \*         revert state back to the negative when done
    State = 0,
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
    unlock = FALSE)
variable
    queueEntry = << >>
begin
Resume_Lock:
    while TRUE do
        assert ~Destroyed;
        if ~StateAction(State, unlock).Resume then
            State := StateAction(State, unlock).NewState;
            unlock := FALSE;
            goto Resume_Return;
        else
            State := StateAction(State, unlock).NewState;
            unlock := FALSE;
        end if;

Resume_GetQueueEntry:
        assert ~Destroyed;
        either
            await Queue = << >>;
            goto Resume_Unlock;
        or
            await Queue # << >>;
            queueEntry := << Head(Queue) >>;
            if queueEntry[1].Type = "Read" then
Resume_DequeueReader:
                assert ~Destroyed;
                \* Someone else may have added something to the queue
                if Head(Queue) # queueEntry[1] then
                    queueEntry := << >>;
                    goto Resume_GetQueueEntry;
                else
                    Queue := Tail(Queue);
Resume_IncrementReaderCount:
                    assert ~Destroyed;
                    AddLock(queueEntry[1]);
                    queueEntry := << >>;
                    State := State - 1;
                    goto Resume_GetQueueEntry;
                end if;
            elsif State = -1 /\ queueEntry[1].Type = "Write" then
Resume_DequeueWriter:
                assert ~Destroyed;
                if Head(Queue) # queueEntry[1] then
                    queueEntry := << >>;
                    goto Resume_GetQueueEntry;
                else
                    Queue := Tail(Queue);
Resume_SetWriterLock:
                    AddLock(queueEntry[1]);
                    queueEntry := << >>;
                    State := 1;
                    goto Resume_Return;
                end if;
            else
                \* The suggested lock is incompatible with the current locks.
                goto Resume_Unlock;
            end if;
        end either;

Resume_Unlock:
        assert ~Destroyed;
        queueEntry := << >>;
        if State = -1 then
            State := 0;
        else
            State := -State;
        end if;

Resume_DoubleCheck:
        assert ~Destroyed;
        if Queue = << >> then
            return;
        end if;
    end while;

Resume_Return:
    return;
end procedure;

fair process Thread \in Threads
begin
Lock:
    either
        \* Become a writer fast.
        await ~Destroyed;
        await State = 0;
        State := 1;
Lock_FastWrite:
        either
            \* Fast writer succeeded.
            await Queue = << >>;
            AddLock(WriteLock(self));
            goto Unlock_Write;
        or
            \* Fast write failed due to other waiters.
            await Queue # << >>;
            AddWaiter(WriteLock(self));
            call ResumeWaiters(TRUE);
            goto Unlock_Write;
        end either;
    or
        \* Enqueue for writer slow.
        await ~Destroyed;
        await State # 0;
        AddWaiter(WriteLock(self));
        call ResumeWaiters(FALSE);

Unlock_Write:
        await WriteLock(self) \in Locks;
        Unlock(WriteLock(self));
        call ResumeWaiters(TRUE);
        goto Lock;       
    
    or
        \* Become a reader fast.
        await ~Destroyed;
        await State >= 2 \/ State = 0;
        if State = 0 then
            State := 2;
        else
            State := State + 1;
        end if;

Lock_FastRead:
        either
            \* Fast reader succeeded.
            await Queue = << >>;
            AddLock(ReadLock(self));
            goto Unlock_Read;
        or
            \* Fast reader failed due to other waiters.
            await Queue # << >>;
            AddWaiter(ReadLock(self));
            call ResumeWaiters(TRUE);
            goto Unlock_Read;
        end either;
    or
        \* Enqueue for reader slow.
        await ~Destroyed;
        await State = 1 \/ State < 0;
        AddWaiter(ReadLock(self));
        call ResumeWaiters(FALSE);

Unlock_Read:
        await ReadLock(self) \in Locks;
        Unlock(ReadLock(self));
        call ResumeWaiters(TRUE);
        goto Lock;

    or
        await Destroyed;
        skip;
    end either;

end process;

fair process Destroy \in { "Destroyer" }
begin
DestroyIfIdle:
    await
        \* Disable destruction for now.
        /\  FALSE
        /\  Queue = << >> 
        /\  Locks = { }
        /\  State <= 0;
    Destroyed := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2f8a165a" /\ chksum(tla) = "be2e79ab")
VARIABLES State, Queue, Locks, Destroyed, pc, stack, unlock, queueEntry

vars == << State, Queue, Locks, Destroyed, pc, stack, unlock, queueEntry >>

ProcSet == (Threads) \cup ({ "Destroyer" })

Init == (* Global variables *)
        /\ State = 0
        /\ Queue = << >>
        /\ Locks = { }
        /\ Destroyed = FALSE
        (* Procedure ResumeWaiters *)
        /\ unlock = [ self \in ProcSet |-> FALSE]
        /\ queueEntry = [ self \in ProcSet |-> << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "Lock"
                                        [] self \in { "Destroyer" } -> "DestroyIfIdle"]

Resume_Lock(self) == /\ pc[self] = "Resume_Lock"
                     /\ Assert(~Destroyed, 
                               "Failure of assertion at line 114, column 9.")
                     /\ IF ~StateAction(State, unlock[self]).Resume
                           THEN /\ State' = StateAction(State, unlock[self]).NewState
                                /\ unlock' = [unlock EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "Resume_Return"]
                           ELSE /\ State' = StateAction(State, unlock[self]).NewState
                                /\ unlock' = [unlock EXCEPT ![self] = FALSE]
                                /\ pc' = [pc EXCEPT ![self] = "Resume_GetQueueEntry"]
                     /\ UNCHANGED << Queue, Locks, Destroyed, stack, 
                                     queueEntry >>

Resume_GetQueueEntry(self) == /\ pc[self] = "Resume_GetQueueEntry"
                              /\ Assert(~Destroyed, 
                                        "Failure of assertion at line 125, column 9.")
                              /\ \/ /\ Queue = << >>
                                    /\ pc' = [pc EXCEPT ![self] = "Resume_Unlock"]
                                    /\ UNCHANGED queueEntry
                                 \/ /\ Queue # << >>
                                    /\ queueEntry' = [queueEntry EXCEPT ![self] = << Head(Queue) >>]
                                    /\ IF queueEntry'[self][1].Type = "Read"
                                          THEN /\ pc' = [pc EXCEPT ![self] = "Resume_DequeueReader"]
                                          ELSE /\ IF State = -1 /\ queueEntry'[self][1].Type = "Write"
                                                     THEN /\ pc' = [pc EXCEPT ![self] = "Resume_DequeueWriter"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Resume_Unlock"]
                              /\ UNCHANGED << State, Queue, Locks, Destroyed, 
                                              stack, unlock >>

Resume_DequeueReader(self) == /\ pc[self] = "Resume_DequeueReader"
                              /\ Assert(~Destroyed, 
                                        "Failure of assertion at line 134, column 17.")
                              /\ IF Head(Queue) # queueEntry[self][1]
                                    THEN /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                                         /\ pc' = [pc EXCEPT ![self] = "Resume_GetQueueEntry"]
                                         /\ Queue' = Queue
                                    ELSE /\ Queue' = Tail(Queue)
                                         /\ pc' = [pc EXCEPT ![self] = "Resume_IncrementReaderCount"]
                                         /\ UNCHANGED queueEntry
                              /\ UNCHANGED << State, Locks, Destroyed, stack, 
                                              unlock >>

Resume_IncrementReaderCount(self) == /\ pc[self] = "Resume_IncrementReaderCount"
                                     /\ Assert(~Destroyed, 
                                               "Failure of assertion at line 142, column 21.")
                                     /\ Locks' = (Locks \union { (queueEntry[self][1]) })
                                     /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                                     /\ State' = State - 1
                                     /\ pc' = [pc EXCEPT ![self] = "Resume_GetQueueEntry"]
                                     /\ UNCHANGED << Queue, Destroyed, stack, 
                                                     unlock >>

Resume_DequeueWriter(self) == /\ pc[self] = "Resume_DequeueWriter"
                              /\ Assert(~Destroyed, 
                                        "Failure of assertion at line 150, column 17.")
                              /\ IF Head(Queue) # queueEntry[self][1]
                                    THEN /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                                         /\ pc' = [pc EXCEPT ![self] = "Resume_GetQueueEntry"]
                                         /\ Queue' = Queue
                                    ELSE /\ Queue' = Tail(Queue)
                                         /\ pc' = [pc EXCEPT ![self] = "Resume_SetWriterLock"]
                                         /\ UNCHANGED queueEntry
                              /\ UNCHANGED << State, Locks, Destroyed, stack, 
                                              unlock >>

Resume_SetWriterLock(self) == /\ pc[self] = "Resume_SetWriterLock"
                              /\ Locks' = (Locks \union { (queueEntry[self][1]) })
                              /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                              /\ State' = 1
                              /\ pc' = [pc EXCEPT ![self] = "Resume_Return"]
                              /\ UNCHANGED << Queue, Destroyed, stack, unlock >>

Resume_Unlock(self) == /\ pc[self] = "Resume_Unlock"
                       /\ Assert(~Destroyed, 
                                 "Failure of assertion at line 169, column 9.")
                       /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                       /\ IF State = -1
                             THEN /\ State' = 0
                             ELSE /\ State' = -State
                       /\ pc' = [pc EXCEPT ![self] = "Resume_DoubleCheck"]
                       /\ UNCHANGED << Queue, Locks, Destroyed, stack, unlock >>

Resume_DoubleCheck(self) == /\ pc[self] = "Resume_DoubleCheck"
                            /\ Assert(~Destroyed, 
                                      "Failure of assertion at line 178, column 9.")
                            /\ IF Queue = << >>
                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                       /\ queueEntry' = [queueEntry EXCEPT ![self] = Head(stack[self]).queueEntry]
                                       /\ unlock' = [unlock EXCEPT ![self] = Head(stack[self]).unlock]
                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                                       /\ UNCHANGED << stack, unlock, 
                                                       queueEntry >>
                            /\ UNCHANGED << State, Queue, Locks, Destroyed >>

Resume_Return(self) == /\ pc[self] = "Resume_Return"
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ queueEntry' = [queueEntry EXCEPT ![self] = Head(stack[self]).queueEntry]
                       /\ unlock' = [unlock EXCEPT ![self] = Head(stack[self]).unlock]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << State, Queue, Locks, Destroyed >>

ResumeWaiters(self) == Resume_Lock(self) \/ Resume_GetQueueEntry(self)
                          \/ Resume_DequeueReader(self)
                          \/ Resume_IncrementReaderCount(self)
                          \/ Resume_DequeueWriter(self)
                          \/ Resume_SetWriterLock(self)
                          \/ Resume_Unlock(self)
                          \/ Resume_DoubleCheck(self)
                          \/ Resume_Return(self)

Lock(self) == /\ pc[self] = "Lock"
              /\ \/ /\ ~Destroyed
                    /\ State = 0
                    /\ State' = 1
                    /\ pc' = [pc EXCEPT ![self] = "Lock_FastWrite"]
                    /\ UNCHANGED <<Queue, stack, unlock, queueEntry>>
                 \/ /\ ~Destroyed
                    /\ State # 0
                    /\ Queue' = Queue \o << (WriteLock(self)) >>
                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                pc        |->  "Unlock_Write",
                                                                queueEntry |->  queueEntry[self],
                                                                unlock    |->  unlock[self] ] >>
                                                            \o stack[self]]
                       /\ unlock' = [unlock EXCEPT ![self] = FALSE]
                    /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                    /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                    /\ State' = State
                 \/ /\ ~Destroyed
                    /\ State >= 2 \/ State = 0
                    /\ IF State = 0
                          THEN /\ State' = 2
                          ELSE /\ State' = State + 1
                    /\ pc' = [pc EXCEPT ![self] = "Lock_FastRead"]
                    /\ UNCHANGED <<Queue, stack, unlock, queueEntry>>
                 \/ /\ ~Destroyed
                    /\ State = 1 \/ State < 0
                    /\ Queue' = Queue \o << (ReadLock(self)) >>
                    /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                pc        |->  "Unlock_Read",
                                                                queueEntry |->  queueEntry[self],
                                                                unlock    |->  unlock[self] ] >>
                                                            \o stack[self]]
                       /\ unlock' = [unlock EXCEPT ![self] = FALSE]
                    /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                    /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                    /\ State' = State
                 \/ /\ Destroyed
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED <<State, Queue, stack, unlock, queueEntry>>
              /\ UNCHANGED << Locks, Destroyed >>

Lock_FastWrite(self) == /\ pc[self] = "Lock_FastWrite"
                        /\ \/ /\ Queue = << >>
                              /\ Locks' = (Locks \union { (WriteLock(self)) })
                              /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                              /\ UNCHANGED <<Queue, stack, unlock, queueEntry>>
                           \/ /\ Queue # << >>
                              /\ Queue' = Queue \o << (WriteLock(self)) >>
                              /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                          pc        |->  "Unlock_Write",
                                                                          queueEntry |->  queueEntry[self],
                                                                          unlock    |->  unlock[self] ] >>
                                                                      \o stack[self]]
                                 /\ unlock' = [unlock EXCEPT ![self] = TRUE]
                              /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                              /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                              /\ Locks' = Locks
                        /\ UNCHANGED << State, Destroyed >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ WriteLock(self) \in Locks
                      /\ Locks' = Locks \ { (WriteLock(self)) }
                      /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                  pc        |->  "Lock",
                                                                  queueEntry |->  queueEntry[self],
                                                                  unlock    |->  unlock[self] ] >>
                                                              \o stack[self]]
                         /\ unlock' = [unlock EXCEPT ![self] = TRUE]
                      /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                      /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                      /\ UNCHANGED << State, Queue, Destroyed >>

Lock_FastRead(self) == /\ pc[self] = "Lock_FastRead"
                       /\ \/ /\ Queue = << >>
                             /\ Locks' = (Locks \union { (ReadLock(self)) })
                             /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                             /\ UNCHANGED <<Queue, stack, unlock, queueEntry>>
                          \/ /\ Queue # << >>
                             /\ Queue' = Queue \o << (ReadLock(self)) >>
                             /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                         pc        |->  "Unlock_Read",
                                                                         queueEntry |->  queueEntry[self],
                                                                         unlock    |->  unlock[self] ] >>
                                                                     \o stack[self]]
                                /\ unlock' = [unlock EXCEPT ![self] = TRUE]
                             /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                             /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                             /\ Locks' = Locks
                       /\ UNCHANGED << State, Destroyed >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ ReadLock(self) \in Locks
                     /\ Locks' = Locks \ { (ReadLock(self)) }
                     /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                 pc        |->  "Lock",
                                                                 queueEntry |->  queueEntry[self],
                                                                 unlock    |->  unlock[self] ] >>
                                                             \o stack[self]]
                        /\ unlock' = [unlock EXCEPT ![self] = TRUE]
                     /\ queueEntry' = [queueEntry EXCEPT ![self] = << >>]
                     /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                     /\ UNCHANGED << State, Queue, Destroyed >>

Thread(self) == Lock(self) \/ Lock_FastWrite(self) \/ Unlock_Write(self)
                   \/ Lock_FastRead(self) \/ Unlock_Read(self)

DestroyIfIdle(self) == /\ pc[self] = "DestroyIfIdle"
                       /\ /\  FALSE
                          /\  Queue = << >>
                          /\  Locks = { }
                          /\  State <= 0
                       /\ Destroyed' = TRUE
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << State, Queue, Locks, stack, unlock, 
                                       queueEntry >>

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
    /\  \A lock \in LockType :
        []<>ENABLED(Queue' = Queue \o << lock >>)

Alias ==
    [
        State |-> State,
        Queue |-> Queue,
        Locks |-> Locks,
        pc |-> pc,
        stack |-> stack,
        unlock |-> unlock,
        queueEntry |-> queueEntry,
        Threads |-> [
            thread \in Threads |-> [
                Lock |-> ENABLED(Lock(thread)),
                Lock_FastRead |-> ENABLED(Lock_FastRead(thread)),
                WriteLockAcquired |-> WriteLock(thread) \in Locks,
                ReadLockAcquired |-> ReadLock(thread) \in Locks
            ]
        ],
        FairLock |-> FairLock!Alias
    ]
==== 
