---- MODULE ReaderWriterLock ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    ReaderCount,
    Queue,
    Locks

AwaiterListType == Seq(Threads)

FairLock == INSTANCE FairReaderWriterLock

TypeOk ==
    /\  ReaderCount \in -2..Cardinality(Threads)
    /\  Queue \in FairLock!QueueType
    /\  Locks \in SUBSET FairLock!LockType

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

(* --algorithm ReaderWriterLock

variables
    ReaderCount = 0,
    Queue = << >>,
    Locks = { };

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

procedure ResumeWaiters(readerDelta = 0)
variable 
    ActualReaderCount = 0;
begin
Resume_Lock:
    \* Acquire the lock on resuming waiters
    ActualReaderCount := ReaderCount + readerDelta;
    ReaderCount := -2;
    readerDelta := 0;
Resume:
    either
        await Queue = << >>;
        ReaderCount := ActualReaderCount;
        return;
    or
        await Queue # << >>;
        if ActualReaderCount >= 0 /\ Head(Queue).Type = "Read" then
            AddLock(Head(Queue));
            ActualReaderCount := ActualReaderCount + 1;
            goto Resume_Dequeue;
        elsif ActualReaderCount = 0 /\ Head(Queue).Type = "Write" then
            ActualReaderCount := -1;
            AddLock(Head(Queue));
            goto Resume_Dequeue;
        else
            goto Resume_Unlock;
        end if;
Resume_Dequeue:
        Queue := Tail(Queue);
    end either;

Resume_Unlock:
    ReaderCount := ActualReaderCount;
    return;
end procedure;

fair process Thread \in Threads
begin
Lock:
    either
        \* Become a writer fast.
        await ReaderCount = 0;
        ReaderCount := -1;
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
            call ResumeWaiters(1);
            goto Unlock_Write;
        end either;
    or
        \* Enqueue for writer slow.
        await Queue # << >>;
        AddWaiter(WriteLock(self));
        goto Unlock_Write;

Lock_Write_ResumeWaiters:
        call ResumeWaiters(0);

Unlock_Write:
        await WriteLock(self) \in Locks;
        Unlock(WriteLock(self));
        call ResumeWaiters(1);
        goto Lock;       
    
    or
        \* Become a reader fast.
        await ReaderCount >= 0;
        ReaderCount := ReaderCount + 1;
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
Lock_FastRead_ResumeWaiters:
            call ResumeWaiters(-1);
            goto Unlock_Read;
        end either;
    or
        \* Enqueue for reader slow.
        await Queue # << >>;
        AddWaiter(ReadLock(self));

Lock_Read_ResumeWaiters:
        call ResumeWaiters(0);

Unlock_Read:
        await ReadLock(self) \in Locks;
        Unlock(ReadLock(self));
        call ResumeWaiters(-1);
        goto Lock;

    end either;

end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "498b51da" /\ chksum(tla) = "6fa4bb24")
VARIABLES ReaderCount, Queue, Locks, pc, stack, readerDelta, 
          ActualReaderCount

vars == << ReaderCount, Queue, Locks, pc, stack, readerDelta, 
           ActualReaderCount >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ ReaderCount = 0
        /\ Queue = << >>
        /\ Locks = { }
        (* Procedure ResumeWaiters *)
        /\ readerDelta = [ self \in ProcSet |-> 0]
        /\ ActualReaderCount = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Lock"]

Resume_Lock(self) == /\ pc[self] = "Resume_Lock"
                     /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = ReaderCount + readerDelta[self]]
                     /\ ReaderCount' = -2
                     /\ readerDelta' = [readerDelta EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "Resume"]
                     /\ UNCHANGED << Queue, Locks, stack >>

Resume(self) == /\ pc[self] = "Resume"
                /\ \/ /\ Queue = << >>
                      /\ ReaderCount' = ActualReaderCount[self]
                      /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                      /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = Head(stack[self]).ActualReaderCount]
                      /\ readerDelta' = [readerDelta EXCEPT ![self] = Head(stack[self]).readerDelta]
                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                      /\ Locks' = Locks
                   \/ /\ Queue # << >>
                      /\ IF ActualReaderCount[self] >= 0 /\ Head(Queue).Type = "Read"
                            THEN /\ Locks' = (Locks \union { (Head(Queue)) })
                                 /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = ActualReaderCount[self] + 1]
                                 /\ pc' = [pc EXCEPT ![self] = "Resume_Dequeue"]
                            ELSE /\ IF ActualReaderCount[self] = 0 /\ Head(Queue).Type = "Write"
                                       THEN /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = -1]
                                            /\ Locks' = (Locks \union { (Head(Queue)) })
                                            /\ pc' = [pc EXCEPT ![self] = "Resume_Dequeue"]
                                       ELSE /\ pc' = [pc EXCEPT ![self] = "Resume_Unlock"]
                                            /\ UNCHANGED << Locks, 
                                                            ActualReaderCount >>
                      /\ UNCHANGED <<ReaderCount, stack, readerDelta>>
                /\ Queue' = Queue

Resume_Dequeue(self) == /\ pc[self] = "Resume_Dequeue"
                        /\ Queue' = Tail(Queue)
                        /\ pc' = [pc EXCEPT ![self] = "Resume_Unlock"]
                        /\ UNCHANGED << ReaderCount, Locks, stack, readerDelta, 
                                        ActualReaderCount >>

Resume_Unlock(self) == /\ pc[self] = "Resume_Unlock"
                       /\ ReaderCount' = ActualReaderCount[self]
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = Head(stack[self]).ActualReaderCount]
                       /\ readerDelta' = [readerDelta EXCEPT ![self] = Head(stack[self]).readerDelta]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << Queue, Locks >>

ResumeWaiters(self) == Resume_Lock(self) \/ Resume(self)
                          \/ Resume_Dequeue(self) \/ Resume_Unlock(self)

Lock(self) == /\ pc[self] = "Lock"
              /\ \/ /\ ReaderCount = 0
                    /\ ReaderCount' = -1
                    /\ pc' = [pc EXCEPT ![self] = "Lock_FastWrite"]
                    /\ Queue' = Queue
                 \/ /\ Queue # << >>
                    /\ Queue' = Queue \o << (WriteLock(self)) >>
                    /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                    /\ UNCHANGED ReaderCount
                 \/ /\ ReaderCount >= 0
                    /\ ReaderCount' = ReaderCount + 1
                    /\ pc' = [pc EXCEPT ![self] = "Lock_FastRead"]
                    /\ Queue' = Queue
                 \/ /\ Queue # << >>
                    /\ Queue' = Queue \o << (ReadLock(self)) >>
                    /\ pc' = [pc EXCEPT ![self] = "Lock_Read_ResumeWaiters"]
                    /\ UNCHANGED ReaderCount
              /\ UNCHANGED << Locks, stack, readerDelta, ActualReaderCount >>

Lock_FastWrite(self) == /\ pc[self] = "Lock_FastWrite"
                        /\ \/ /\ Queue = << >>
                              /\ Locks' = (Locks \union { (WriteLock(self)) })
                              /\ pc' = [pc EXCEPT ![self] = "Unlock_Write"]
                              /\ UNCHANGED <<Queue, stack, readerDelta, ActualReaderCount>>
                           \/ /\ Queue # << >>
                              /\ Queue' = Queue \o << (WriteLock(self)) >>
                              /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = 1]
                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                          pc        |->  "Unlock_Write",
                                                                          ActualReaderCount |->  ActualReaderCount[self],
                                                                          readerDelta |->  readerDelta[self] ] >>
                                                                      \o stack[self]]
                              /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                              /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                              /\ Locks' = Locks
                        /\ UNCHANGED ReaderCount

Lock_Write_ResumeWaiters(self) == /\ pc[self] = "Lock_Write_ResumeWaiters"
                                  /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = 0]
                                     /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                              pc        |->  "Unlock_Write",
                                                                              ActualReaderCount |->  ActualReaderCount[self],
                                                                              readerDelta |->  readerDelta[self] ] >>
                                                                          \o stack[self]]
                                  /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                                  /\ UNCHANGED << ReaderCount, Queue, Locks >>

Unlock_Write(self) == /\ pc[self] = "Unlock_Write"
                      /\ WriteLock(self) \in Locks
                      /\ Locks' = Locks \ { (WriteLock(self)) }
                      /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = 1]
                         /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                  pc        |->  "Lock",
                                                                  ActualReaderCount |->  ActualReaderCount[self],
                                                                  readerDelta |->  readerDelta[self] ] >>
                                                              \o stack[self]]
                      /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                      /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                      /\ UNCHANGED << ReaderCount, Queue >>

Lock_FastRead(self) == /\ pc[self] = "Lock_FastRead"
                       /\ \/ /\ Queue = << >>
                             /\ Locks' = (Locks \union { (ReadLock(self)) })
                             /\ pc' = [pc EXCEPT ![self] = "Unlock_Read"]
                             /\ Queue' = Queue
                          \/ /\ Queue # << >>
                             /\ Queue' = Queue \o << (ReadLock(self)) >>
                             /\ pc' = [pc EXCEPT ![self] = "Lock_FastRead_ResumeWaiters"]
                             /\ Locks' = Locks
                       /\ UNCHANGED << ReaderCount, stack, readerDelta, 
                                       ActualReaderCount >>

Lock_FastRead_ResumeWaiters(self) == /\ pc[self] = "Lock_FastRead_ResumeWaiters"
                                     /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = -1]
                                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                                 pc        |->  "Unlock_Read",
                                                                                 ActualReaderCount |->  ActualReaderCount[self],
                                                                                 readerDelta |->  readerDelta[self] ] >>
                                                                             \o stack[self]]
                                     /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                                     /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                                     /\ UNCHANGED << ReaderCount, Queue, Locks >>

Lock_Read_ResumeWaiters(self) == /\ pc[self] = "Lock_Read_ResumeWaiters"
                                 /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = 0]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                             pc        |->  "Unlock_Read",
                                                                             ActualReaderCount |->  ActualReaderCount[self],
                                                                             readerDelta |->  readerDelta[self] ] >>
                                                                         \o stack[self]]
                                 /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                                 /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                                 /\ UNCHANGED << ReaderCount, Queue, Locks >>

Unlock_Read(self) == /\ pc[self] = "Unlock_Read"
                     /\ ReadLock(self) \in Locks
                     /\ Locks' = Locks \ { (ReadLock(self)) }
                     /\ /\ readerDelta' = [readerDelta EXCEPT ![self] = -1]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeWaiters",
                                                                 pc        |->  "Lock",
                                                                 ActualReaderCount |->  ActualReaderCount[self],
                                                                 readerDelta |->  readerDelta[self] ] >>
                                                             \o stack[self]]
                     /\ ActualReaderCount' = [ActualReaderCount EXCEPT ![self] = 0]
                     /\ pc' = [pc EXCEPT ![self] = "Resume_Lock"]
                     /\ UNCHANGED << ReaderCount, Queue >>

Thread(self) == Lock(self) \/ Lock_FastWrite(self)
                   \/ Lock_Write_ResumeWaiters(self) \/ Unlock_Write(self)
                   \/ Lock_FastRead(self)
                   \/ Lock_FastRead_ResumeWaiters(self)
                   \/ Lock_Read_ResumeWaiters(self) \/ Unlock_Read(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: ResumeWaiters(self))
           \/ (\E self \in Threads: Thread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(Thread(self)) /\ WF_vars(ResumeWaiters(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Property ==
    /\  FairLock!Spec
    /\  []TypeOk

==== 
