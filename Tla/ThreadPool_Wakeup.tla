----------------------------- MODULE ThreadPool_Wakeup -----------------------------
EXTENDS Sequences, Naturals, Integers, TLC, FiniteSets
CONSTANT WorkerThreads, RemoteThreads, Items

ASSUME Cardinality(WorkerThreads) > 0
ASSUME Cardinality(RemoteThreads) > 0

Threads == WorkerThreads \union RemoteThreads

(* --algorithm ThreadPool_Wakeup

variables 
    Queues = [thread \in Threads |-> 0],
    PendingItems = Items,
    ProcessedItems = 0,
    SleepingThreads = 0,
    IntentsToSleep = [thread \in Threads |-> FALSE],
    WakeSignals = [thread \in Threads |-> FALSE];

macro EnqueueItem(thread)
begin
    await PendingItems > 0;
    Queues[thread] := Queues[thread] + 1;
    PendingItems := PendingItems - 1;
end macro;

procedure WakeThread(threadNotToSignal = {})
    variables ThreadToWake = {};
begin
WakeThread_CheckSleepingThreads:
    if SleepingThreads = 0 then
        return;
    else
        SleepingThreads := SleepingThreads - 1;
    end if;

WakeThread_FindThreadToWake:
    with threadToWake \in Threads do
        await IntentsToSleep[threadToWake] = TRUE;
        ThreadToWake := threadToWake;
        IntentsToSleep[threadToWake] := FALSE;
    end with;
    
WakeThread_SignalThread:
    if (ThreadToWake # threadNotToSignal) then
        WakeSignals[ThreadToWake] := TRUE;
    end if;
    return;

end procedure;

fair process remoteThread \in RemoteThreads
begin
RemoteThread:
    EnqueueItem(self);
    call WakeThread(self);
    goto RemoteThread;
end process;

fair process workerThread \in WorkerThreads
variables
    UncheckedQueues = Threads;

begin
    Processing:
        UncheckedQueues := Threads;
        if ItemToProcess > 0 then
            ItemToProcess := ItemToProcess - 1;
            goto ProcessItem;
        elsif Queues[self] # 0 then
            Queues[self] := Queues[self] - 1;
            goto ProcessItem;
        end if;

    IntendToSleep_MarkIntent:
        if IntentsToSleep[self] = TRUE then
            goto IntendToSleep_CheckRemoteQueues;
        else
            IntentsToSleep[self] := TRUE;
        end if;    

    IntendToSleep_IncrementSleepingThreads:
        SleepingThreads := SleepingThreads + 1;

    IntendToSleep_CheckRemoteQueues:
        while UncheckedQueues # {} do
            with uncheckedQueue \in UncheckedQueues do
                if Queues[uncheckedQueue] # 0 then
                    with itemsToSteal \in 1..Queues[uncheckedQueue] do
                        Queues[uncheckedQueue] := Queues[uncheckedQueue] - itemsToSteal
                        ||
                        Queues[self] := Queues[self] + itemsToSteal - 1;
                    end with;
                    goto Remove_IntentToSleep;
                else
                    UncheckedQueues := UncheckedQueues \ { uncheckedQueue };
                end if;
            end with;
        end while;

    Sleep:
        await WakeSignals[self] = TRUE;
        WakeSignals[self] := FALSE;
        goto Processing;

    Remove_IntentToSleep:
        call WakeThread(self);

    ProcessItem:
        either
            EnqueueItem(self);
            call WakeThread(self);
            goto ProcessItem;
        or
            ProcessedItems := ProcessedItems + 1;
            goto Processing;
        end either;

end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a9fe21d0" /\ chksum(tla) = "6a7d99ab")
VARIABLES Queues, PendingItems, ProcessedItems, SleepingThreads, 
          IntentsToSleep, WakeSignals, pc, stack, threadNotToSignal, 
          ThreadToWake, ItemToProcess, UncheckedQueues

vars == << Queues, PendingItems, ProcessedItems, SleepingThreads, 
           IntentsToSleep, WakeSignals, pc, stack, threadNotToSignal, 
           ThreadToWake, ItemToProcess, UncheckedQueues >>

ProcSet == (RemoteThreads) \cup (WorkerThreads)

Init == (* Global variables *)
        /\ Queues = [thread \in Threads |-> 0]
        /\ PendingItems = Items
        /\ ProcessedItems = 0
        /\ SleepingThreads = 0
        /\ IntentsToSleep = [thread \in Threads |-> FALSE]
        /\ WakeSignals = [thread \in Threads |-> FALSE]
        (* Procedure WakeThread *)
        /\ threadNotToSignal = [ self \in ProcSet |-> {}]
        /\ ThreadToWake = [ self \in ProcSet |-> {}]
        (* Process workerThread *)
        /\ ItemToProcess = [self \in WorkerThreads |-> 0]
        /\ UncheckedQueues = [self \in WorkerThreads |-> Threads]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in RemoteThreads -> "RemoteThread"
                                        [] self \in WorkerThreads -> "Processing"]

WakeThread_CheckSleepingThreads(self) == /\ pc[self] = "WakeThread_CheckSleepingThreads"
                                         /\ IF SleepingThreads = 0
                                               THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                                    /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = Head(stack[self]).ThreadToWake]
                                                    /\ threadNotToSignal' = [threadNotToSignal EXCEPT ![self] = Head(stack[self]).threadNotToSignal]
                                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                                    /\ UNCHANGED SleepingThreads
                                               ELSE /\ SleepingThreads' = SleepingThreads - 1
                                                    /\ pc' = [pc EXCEPT ![self] = "WakeThread_FindThreadToWake"]
                                                    /\ UNCHANGED << stack, 
                                                                    threadNotToSignal, 
                                                                    ThreadToWake >>
                                         /\ UNCHANGED << Queues, PendingItems, 
                                                         ProcessedItems, 
                                                         IntentsToSleep, 
                                                         WakeSignals, 
                                                         ItemToProcess, 
                                                         UncheckedQueues >>

WakeThread_FindThreadToWake(self) == /\ pc[self] = "WakeThread_FindThreadToWake"
                                     /\ \E threadToWake \in Threads:
                                          /\ IntentsToSleep[threadToWake] = TRUE
                                          /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = threadToWake]
                                          /\ IntentsToSleep' = [IntentsToSleep EXCEPT ![threadToWake] = FALSE]
                                     /\ pc' = [pc EXCEPT ![self] = "WakeThread_SignalThread"]
                                     /\ UNCHANGED << Queues, PendingItems, 
                                                     ProcessedItems, 
                                                     SleepingThreads, 
                                                     WakeSignals, stack, 
                                                     threadNotToSignal, 
                                                     ItemToProcess, 
                                                     UncheckedQueues >>

WakeThread_SignalThread(self) == /\ pc[self] = "WakeThread_SignalThread"
                                 /\ IF (ThreadToWake[self] # threadNotToSignal[self])
                                       THEN /\ WakeSignals' = [WakeSignals EXCEPT ![ThreadToWake[self]] = TRUE]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED WakeSignals
                                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                 /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = Head(stack[self]).ThreadToWake]
                                 /\ threadNotToSignal' = [threadNotToSignal EXCEPT ![self] = Head(stack[self]).threadNotToSignal]
                                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                 /\ UNCHANGED << Queues, PendingItems, 
                                                 ProcessedItems, 
                                                 SleepingThreads, 
                                                 IntentsToSleep, ItemToProcess, 
                                                 UncheckedQueues >>

WakeThread(self) == WakeThread_CheckSleepingThreads(self)
                       \/ WakeThread_FindThreadToWake(self)
                       \/ WakeThread_SignalThread(self)

RemoteThread(self) == /\ pc[self] = "RemoteThread"
                      /\ PendingItems > 0
                      /\ Queues' = [Queues EXCEPT ![self] = Queues[self] + 1]
                      /\ PendingItems' = PendingItems - 1
                      /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "WakeThread",
                                                                  pc        |->  "RemoteThread",
                                                                  ThreadToWake |->  ThreadToWake[self],
                                                                  threadNotToSignal |->  threadNotToSignal[self] ] >>
                                                              \o stack[self]]
                         /\ threadNotToSignal' = [threadNotToSignal EXCEPT ![self] = self]
                      /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = {}]
                      /\ pc' = [pc EXCEPT ![self] = "WakeThread_CheckSleepingThreads"]
                      /\ UNCHANGED << ProcessedItems, SleepingThreads, 
                                      IntentsToSleep, WakeSignals, 
                                      ItemToProcess, UncheckedQueues >>

remoteThread(self) == RemoteThread(self)

Processing(self) == /\ pc[self] = "Processing"
                    /\ UncheckedQueues' = [UncheckedQueues EXCEPT ![self] = Threads]
                    /\ IF ItemToProcess[self] > 0
                          THEN /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = ItemToProcess[self] - 1]
                               /\ pc' = [pc EXCEPT ![self] = "ProcessItem"]
                               /\ UNCHANGED Queues
                          ELSE /\ IF Queues[self] # 0
                                     THEN /\ Queues' = [Queues EXCEPT ![self] = Queues[self] - 1]
                                          /\ pc' = [pc EXCEPT ![self] = "ProcessItem"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "IntendToSleep_MarkIntent"]
                                          /\ UNCHANGED Queues
                               /\ UNCHANGED ItemToProcess
                    /\ UNCHANGED << PendingItems, ProcessedItems, 
                                    SleepingThreads, IntentsToSleep, 
                                    WakeSignals, stack, threadNotToSignal, 
                                    ThreadToWake >>

IntendToSleep_MarkIntent(self) == /\ pc[self] = "IntendToSleep_MarkIntent"
                                  /\ IF IntentsToSleep[self] = TRUE
                                        THEN /\ pc' = [pc EXCEPT ![self] = "IntendToSleep_CheckRemoteQueues"]
                                             /\ UNCHANGED IntentsToSleep
                                        ELSE /\ IntentsToSleep' = [IntentsToSleep EXCEPT ![self] = TRUE]
                                             /\ pc' = [pc EXCEPT ![self] = "IntendToSleep_IncrementSleepingThreads"]
                                  /\ UNCHANGED << Queues, PendingItems, 
                                                  ProcessedItems, 
                                                  SleepingThreads, WakeSignals, 
                                                  stack, threadNotToSignal, 
                                                  ThreadToWake, ItemToProcess, 
                                                  UncheckedQueues >>

IntendToSleep_IncrementSleepingThreads(self) == /\ pc[self] = "IntendToSleep_IncrementSleepingThreads"
                                                /\ SleepingThreads' = SleepingThreads + 1
                                                /\ pc' = [pc EXCEPT ![self] = "IntendToSleep_CheckRemoteQueues"]
                                                /\ UNCHANGED << Queues, 
                                                                PendingItems, 
                                                                ProcessedItems, 
                                                                IntentsToSleep, 
                                                                WakeSignals, 
                                                                stack, 
                                                                threadNotToSignal, 
                                                                ThreadToWake, 
                                                                ItemToProcess, 
                                                                UncheckedQueues >>

IntendToSleep_CheckRemoteQueues(self) == /\ pc[self] = "IntendToSleep_CheckRemoteQueues"
                                         /\ IF UncheckedQueues[self] # {}
                                               THEN /\ \E uncheckedQueue \in UncheckedQueues[self]:
                                                         IF Queues[uncheckedQueue] # 0
                                                            THEN /\ \E itemsToSteal \in 1..Queues[uncheckedQueue]:
                                                                      /\ ItemToProcess' = [ItemToProcess EXCEPT ![self] = 1]
                                                                      /\ Queues' = [Queues EXCEPT ![uncheckedQueue] = Queues[uncheckedQueue] - itemsToSteal,
                                                                                                  ![self] = Queues[self] + itemsToSteal - 1]
                                                                 /\ pc' = [pc EXCEPT ![self] = "Remove_IntentToSleep"]
                                                                 /\ UNCHANGED UncheckedQueues
                                                            ELSE /\ UncheckedQueues' = [UncheckedQueues EXCEPT ![self] = UncheckedQueues[self] \ { uncheckedQueue }]
                                                                 /\ pc' = [pc EXCEPT ![self] = "IntendToSleep_CheckRemoteQueues"]
                                                                 /\ UNCHANGED << Queues, 
                                                                                 ItemToProcess >>
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "Sleep"]
                                                    /\ UNCHANGED << Queues, 
                                                                    ItemToProcess, 
                                                                    UncheckedQueues >>
                                         /\ UNCHANGED << PendingItems, 
                                                         ProcessedItems, 
                                                         SleepingThreads, 
                                                         IntentsToSleep, 
                                                         WakeSignals, stack, 
                                                         threadNotToSignal, 
                                                         ThreadToWake >>

Sleep(self) == /\ pc[self] = "Sleep"
               /\ WakeSignals[self] = TRUE
               /\ WakeSignals' = [WakeSignals EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "Processing"]
               /\ UNCHANGED << Queues, PendingItems, ProcessedItems, 
                               SleepingThreads, IntentsToSleep, stack, 
                               threadNotToSignal, ThreadToWake, ItemToProcess, 
                               UncheckedQueues >>

Remove_IntentToSleep(self) == /\ pc[self] = "Remove_IntentToSleep"
                              /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "WakeThread",
                                                                          pc        |->  "Processing",
                                                                          ThreadToWake |->  ThreadToWake[self],
                                                                          threadNotToSignal |->  threadNotToSignal[self] ] >>
                                                                      \o stack[self]]
                                 /\ threadNotToSignal' = [threadNotToSignal EXCEPT ![self] = self]
                              /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = {}]
                              /\ pc' = [pc EXCEPT ![self] = "WakeThread_CheckSleepingThreads"]
                              /\ UNCHANGED << Queues, PendingItems, 
                                              ProcessedItems, SleepingThreads, 
                                              IntentsToSleep, WakeSignals, 
                                              ItemToProcess, UncheckedQueues >>

ProcessItem(self) == /\ pc[self] = "ProcessItem"
                     /\ \/ /\ PendingItems > 0
                           /\ Queues' = [Queues EXCEPT ![self] = Queues[self] + 1]
                           /\ PendingItems' = PendingItems - 1
                           /\ /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "WakeThread",
                                                                       pc        |->  "ProcessItem",
                                                                       ThreadToWake |->  ThreadToWake[self],
                                                                       threadNotToSignal |->  threadNotToSignal[self] ] >>
                                                                   \o stack[self]]
                              /\ threadNotToSignal' = [threadNotToSignal EXCEPT ![self] = self]
                           /\ ThreadToWake' = [ThreadToWake EXCEPT ![self] = {}]
                           /\ pc' = [pc EXCEPT ![self] = "WakeThread_CheckSleepingThreads"]
                           /\ UNCHANGED ProcessedItems
                        \/ /\ ProcessedItems' = ProcessedItems + 1
                           /\ pc' = [pc EXCEPT ![self] = "Processing"]
                           /\ UNCHANGED <<Queues, PendingItems, stack, threadNotToSignal, ThreadToWake>>
                     /\ UNCHANGED << SleepingThreads, IntentsToSleep, 
                                     WakeSignals, ItemToProcess, 
                                     UncheckedQueues >>

workerThread(self) == Processing(self) \/ IntendToSleep_MarkIntent(self)
                         \/ IntendToSleep_IncrementSleepingThreads(self)
                         \/ IntendToSleep_CheckRemoteQueues(self)
                         \/ Sleep(self) \/ Remove_IntentToSleep(self)
                         \/ ProcessItem(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: WakeThread(self))
           \/ (\E self \in RemoteThreads: remoteThread(self))
           \/ (\E self \in WorkerThreads: workerThread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RemoteThreads : WF_vars(remoteThread(self)) /\ WF_vars(WakeThread(self))
        /\ \A self \in WorkerThreads : WF_vars(workerThread(self)) /\ WF_vars(WakeThread(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

AllItemsGetProcessed ==
    /\  []<>(ProcessedItems = Items)

EventuallyEverythingSleeps ==
    /\  []<>(\A thread \in WorkerThreads : pc[thread] = "Sleep")

EnqueueCanAlwaysMakeProgress == TRUE

=============================================================================
