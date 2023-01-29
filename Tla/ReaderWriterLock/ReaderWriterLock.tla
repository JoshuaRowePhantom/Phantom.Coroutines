---- MODULE ReaderWriterLock ----
EXTENDS Integers, TLC, Sequences

CONSTANT ThreadCount

Threads == 1..ThreadCount

VARIABLE
    WaitingReaders,
    WaitingWriters,
    ReaderCount,
    AcquiredLocks

AwaiterListType == Seq(Threads)

TypeOk ==
    /\  ReaderCount \in Int
    /\  WaitingReaders \in AwaiterListType
    /\  WaitingWriters \in AwaiterListType
    /\  AcquiredLocks \in [ Threads -> { "Blocked", "Read", "Write", "Unlocked" }]

(* --algorithm ReaderWriterLock

variables
    WaitingReaders = << >>,
    WaitingWriters = << >>,
    ReaderCount = 0,
    AcquiredLocks = [ thread \in Threads |-> "Unlocked" ];

procedure SignalWaiters()
variables
    HaveWaitingWriters = WaitingWriters # << >>
begin
SignalWaiters_Loop:
    while TRUE do
        
        HaveWaitingWriters := WaitingWriters # << >>;

SignalWaiters_CheckForWriters:
        if ReaderCount = -1 then
            \* The lock is locked by a writer
            return;
            
        elsif ReaderCount = 0 /\ HaveWaitingWriters then
            \* Provisionally acquire the lock for write.
            ReaderCount := -1;
SignalWaiters_CheckAvailableWriter:
            if WaitingWriters # << >> then
                AcquiredLocks[Head(WaitingWriters)] := "Write";
                WaitingWriters := Tail(WaitingWriters);
                return;
            end if;
SignalWaiters_NoAvailableWriter:
            ReaderCount := 0;
            goto SignalWaiters_Loop;
        end if;

SignalWaiters_CheckWaitingReaders:
        if WaitingReaders = << >> then
            return;
        end if;

SignalWaiters_IncrementReaderCount:
        if ReaderCount < 0 then
            return;
        else
            ReaderCount := ReaderCount + 1;
        end if;

SignalWaiters_SignalReader:
        if WaitingReaders # << >> then            
            AcquiredLocks[Head(WaitingReaders)] := "Read";
            WaitingReaders := Tail(WaitingReaders);
        else
            ReaderCount := ReaderCount - 1;
        end if;
    end while;

end procedure;

procedure LockReader()
begin
LockReader_Start:
    if ReaderCount >= 0 then
        ReaderCount := ReaderCount + 1;
        AcquiredLocks[self] := "Read";
        return;
    end if;

LockReader_Append:
    WaitingReaders := << self >> \o WaitingReaders;
    call SignalWaiters();

LockReader_Wait:
    await AcquiredLocks[self] = "Read";
    return;
end procedure;

procedure UnlockReader()
begin
UnlockReader_Start:
    ReaderCount := ReaderCount - 1;
    AcquiredLocks[self] := "Unlocked";
    call SignalWaiters();
    return;
end procedure;

procedure LockWriter()
begin
LockWriter_Start:
    if ReaderCount = 0 then
        ReaderCount := -1;
        AcquiredLocks[self] := "Write";
        return;
    end if;

LockWriter_Append:
    WaitingWriters := << self >> \o WaitingWriters;
    call SignalWaiters();
    
LockWriter_Wait:
    await AcquiredLocks[self] = "Write";
    return;

end procedure;

procedure UnlockWriter()
begin
UnlockWriter_Start:
    ReaderCount := 0;
    AcquiredLocks[self] := "Unlocked";
    call SignalWaiters();
    return;
end procedure;

fair process Worker \in Threads
begin
Start:
    either
        call LockReader();
UnlockReader:
        call UnlockReader();
    or
        call LockWriter();
UnlockWriter:
        call UnlockWriter();
    end either;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8fde6654" /\ chksum(tla) = "add427be")
\* Label UnlockReader of process Worker at line 142 col 9 changed to UnlockReader_
\* Label UnlockWriter of process Worker at line 146 col 9 changed to UnlockWriter_
VARIABLES WaitingReaders, WaitingWriters, ReaderCount, AcquiredLocks, pc, 
          stack, HaveWaitingWriters

vars == << WaitingReaders, WaitingWriters, ReaderCount, AcquiredLocks, pc, 
           stack, HaveWaitingWriters >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ WaitingReaders = << >>
        /\ WaitingWriters = << >>
        /\ ReaderCount = 0
        /\ AcquiredLocks = [ thread \in Threads |-> "Unlocked" ]
        (* Procedure SignalWaiters *)
        /\ HaveWaitingWriters = [ self \in ProcSet |-> WaitingWriters # << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Start"]

SignalWaiters_Loop(self) == /\ pc[self] = "SignalWaiters_Loop"
                            /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = WaitingWriters # << >>]
                            /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_CheckForWriters"]
                            /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                            ReaderCount, AcquiredLocks, stack >>

SignalWaiters_CheckForWriters(self) == /\ pc[self] = "SignalWaiters_CheckForWriters"
                                       /\ IF ReaderCount = -1
                                             THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                  /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = Head(stack[self]).HaveWaitingWriters]
                                                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                  /\ UNCHANGED ReaderCount
                                             ELSE /\ IF ReaderCount = 0 /\ HaveWaitingWriters[self]
                                                        THEN /\ ReaderCount' = -1
                                                             /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_CheckAvailableWriter"]
                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_CheckWaitingReaders"]
                                                             /\ UNCHANGED ReaderCount
                                                  /\ UNCHANGED << stack, 
                                                                  HaveWaitingWriters >>
                                       /\ UNCHANGED << WaitingReaders, 
                                                       WaitingWriters, 
                                                       AcquiredLocks >>

SignalWaiters_CheckAvailableWriter(self) == /\ pc[self] = "SignalWaiters_CheckAvailableWriter"
                                            /\ IF WaitingWriters # << >>
                                                  THEN /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![Head(WaitingWriters)] = "Write"]
                                                       /\ WaitingWriters' = Tail(WaitingWriters)
                                                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                       /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = Head(stack[self]).HaveWaitingWriters]
                                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                  ELSE /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_NoAvailableWriter"]
                                                       /\ UNCHANGED << WaitingWriters, 
                                                                       AcquiredLocks, 
                                                                       stack, 
                                                                       HaveWaitingWriters >>
                                            /\ UNCHANGED << WaitingReaders, 
                                                            ReaderCount >>

SignalWaiters_NoAvailableWriter(self) == /\ pc[self] = "SignalWaiters_NoAvailableWriter"
                                         /\ ReaderCount' = 0
                                         /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                                         /\ UNCHANGED << WaitingReaders, 
                                                         WaitingWriters, 
                                                         AcquiredLocks, stack, 
                                                         HaveWaitingWriters >>

SignalWaiters_CheckWaitingReaders(self) == /\ pc[self] = "SignalWaiters_CheckWaitingReaders"
                                           /\ IF WaitingReaders = << >>
                                                 THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                      /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = Head(stack[self]).HaveWaitingWriters]
                                                      /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                 ELSE /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_IncrementReaderCount"]
                                                      /\ UNCHANGED << stack, 
                                                                      HaveWaitingWriters >>
                                           /\ UNCHANGED << WaitingReaders, 
                                                           WaitingWriters, 
                                                           ReaderCount, 
                                                           AcquiredLocks >>

SignalWaiters_IncrementReaderCount(self) == /\ pc[self] = "SignalWaiters_IncrementReaderCount"
                                            /\ IF ReaderCount < 0
                                                  THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                       /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = Head(stack[self]).HaveWaitingWriters]
                                                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                       /\ UNCHANGED ReaderCount
                                                  ELSE /\ ReaderCount' = ReaderCount + 1
                                                       /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_SignalReader"]
                                                       /\ UNCHANGED << stack, 
                                                                       HaveWaitingWriters >>
                                            /\ UNCHANGED << WaitingReaders, 
                                                            WaitingWriters, 
                                                            AcquiredLocks >>

SignalWaiters_SignalReader(self) == /\ pc[self] = "SignalWaiters_SignalReader"
                                    /\ IF WaitingReaders # << >>
                                          THEN /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![Head(WaitingReaders)] = "Read"]
                                               /\ WaitingReaders' = Tail(WaitingReaders)
                                               /\ UNCHANGED ReaderCount
                                          ELSE /\ ReaderCount' = ReaderCount - 1
                                               /\ UNCHANGED << WaitingReaders, 
                                                               AcquiredLocks >>
                                    /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                                    /\ UNCHANGED << WaitingWriters, stack, 
                                                    HaveWaitingWriters >>

SignalWaiters(self) == SignalWaiters_Loop(self)
                          \/ SignalWaiters_CheckForWriters(self)
                          \/ SignalWaiters_CheckAvailableWriter(self)
                          \/ SignalWaiters_NoAvailableWriter(self)
                          \/ SignalWaiters_CheckWaitingReaders(self)
                          \/ SignalWaiters_IncrementReaderCount(self)
                          \/ SignalWaiters_SignalReader(self)

LockReader_Start(self) == /\ pc[self] = "LockReader_Start"
                          /\ IF ReaderCount >= 0
                                THEN /\ ReaderCount' = ReaderCount + 1
                                     /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Read"]
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "LockReader_Append"]
                                     /\ UNCHANGED << ReaderCount, 
                                                     AcquiredLocks, stack >>
                          /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                          HaveWaitingWriters >>

LockReader_Append(self) == /\ pc[self] = "LockReader_Append"
                           /\ WaitingReaders' = << self >> \o WaitingReaders
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SignalWaiters",
                                                                    pc        |->  "LockReader_Wait",
                                                                    HaveWaitingWriters |->  HaveWaitingWriters[self] ] >>
                                                                \o stack[self]]
                           /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = WaitingWriters # << >>]
                           /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                           /\ UNCHANGED << WaitingWriters, ReaderCount, 
                                           AcquiredLocks >>

LockReader_Wait(self) == /\ pc[self] = "LockReader_Wait"
                         /\ AcquiredLocks[self] = "Read"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                         ReaderCount, AcquiredLocks, 
                                         HaveWaitingWriters >>

LockReader(self) == LockReader_Start(self) \/ LockReader_Append(self)
                       \/ LockReader_Wait(self)

UnlockReader_Start(self) == /\ pc[self] = "UnlockReader_Start"
                            /\ ReaderCount' = ReaderCount - 1
                            /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Unlocked"]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SignalWaiters",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     HaveWaitingWriters |->  HaveWaitingWriters[self] ] >>
                                                                 \o Tail(stack[self])]
                            /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = WaitingWriters # << >>]
                            /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                            /\ UNCHANGED << WaitingReaders, WaitingWriters >>

UnlockReader(self) == UnlockReader_Start(self)

LockWriter_Start(self) == /\ pc[self] = "LockWriter_Start"
                          /\ IF ReaderCount = 0
                                THEN /\ ReaderCount' = -1
                                     /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Write"]
                                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "LockWriter_Append"]
                                     /\ UNCHANGED << ReaderCount, 
                                                     AcquiredLocks, stack >>
                          /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                          HaveWaitingWriters >>

LockWriter_Append(self) == /\ pc[self] = "LockWriter_Append"
                           /\ WaitingWriters' = << self >> \o WaitingWriters
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SignalWaiters",
                                                                    pc        |->  "LockWriter_Wait",
                                                                    HaveWaitingWriters |->  HaveWaitingWriters[self] ] >>
                                                                \o stack[self]]
                           /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = WaitingWriters' # << >>]
                           /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                           /\ UNCHANGED << WaitingReaders, ReaderCount, 
                                           AcquiredLocks >>

LockWriter_Wait(self) == /\ pc[self] = "LockWriter_Wait"
                         /\ AcquiredLocks[self] = "Write"
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                         ReaderCount, AcquiredLocks, 
                                         HaveWaitingWriters >>

LockWriter(self) == LockWriter_Start(self) \/ LockWriter_Append(self)
                       \/ LockWriter_Wait(self)

UnlockWriter_Start(self) == /\ pc[self] = "UnlockWriter_Start"
                            /\ ReaderCount' = 0
                            /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Unlocked"]
                            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "SignalWaiters",
                                                                     pc        |->  Head(stack[self]).pc,
                                                                     HaveWaitingWriters |->  HaveWaitingWriters[self] ] >>
                                                                 \o Tail(stack[self])]
                            /\ HaveWaitingWriters' = [HaveWaitingWriters EXCEPT ![self] = WaitingWriters # << >>]
                            /\ pc' = [pc EXCEPT ![self] = "SignalWaiters_Loop"]
                            /\ UNCHANGED << WaitingReaders, WaitingWriters >>

UnlockWriter(self) == UnlockWriter_Start(self)

Start(self) == /\ pc[self] = "Start"
               /\ \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LockReader",
                                                              pc        |->  "UnlockReader_" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "LockReader_Start"]
                  \/ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "LockWriter",
                                                              pc        |->  "UnlockWriter_" ] >>
                                                          \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "LockWriter_Start"]
               /\ UNCHANGED << WaitingReaders, WaitingWriters, ReaderCount, 
                               AcquiredLocks, HaveWaitingWriters >>

UnlockReader_(self) == /\ pc[self] = "UnlockReader_"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UnlockReader",
                                                                pc        |->  "Done" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "UnlockReader_Start"]
                       /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                       ReaderCount, AcquiredLocks, 
                                       HaveWaitingWriters >>

UnlockWriter_(self) == /\ pc[self] = "UnlockWriter_"
                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "UnlockWriter",
                                                                pc        |->  "Done" ] >>
                                                            \o stack[self]]
                       /\ pc' = [pc EXCEPT ![self] = "UnlockWriter_Start"]
                       /\ UNCHANGED << WaitingReaders, WaitingWriters, 
                                       ReaderCount, AcquiredLocks, 
                                       HaveWaitingWriters >>

Worker(self) == Start(self) \/ UnlockReader_(self) \/ UnlockWriter_(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ SignalWaiters(self) \/ LockReader(self)
                               \/ UnlockReader(self) \/ LockWriter(self)
                               \/ UnlockWriter(self))
           \/ (\E self \in Threads: Worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : /\ WF_vars(Worker(self))
                                 /\ WF_vars(LockReader(self))
                                 /\ WF_vars(UnlockReader(self))
                                 /\ WF_vars(LockWriter(self))
                                 /\ WF_vars(UnlockWriter(self))
                                 /\ WF_vars(SignalWaiters(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AllLocksAreCompatible ==
    \/  /\  \A thread \in Threads : AcquiredLocks[thread] \in { "Read", "Unlocked" }
    \/  /\  \A thread1, thread2 \in Threads : 
            /\  AcquiredLocks[thread1] \in { "Write", "Unlocked" }
            /\  (
                    /\  AcquiredLocks[thread1] = "Write"
                    /\  AcquiredLocks[thread2] = "Write"
                ) => (thread1 = thread2)

==== 
