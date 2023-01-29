---- MODULE ReaderWriterLock ----
EXTENDS Integers, TLC, Sequences, FiniteSets

CONSTANT Threads

VARIABLE
    ReaderCount,
    ReaderCountWaiters,
    ReaderCountOwner,
    ResourceWaiters,
    ResourceOwner,
    ServiceQueue,
    ServiceQueueOwner,
    AcquiredLocks

AwaiterListType == Seq(Threads)

TypeOk ==
    /\  ReaderCount \in 0..Cardinality(Threads)
    /\  ReaderCountWaiters \in AwaiterListType
    /\  ReaderCountOwner \in AwaiterListType
    /\  ResourceWaiters \in AwaiterListType
    /\  ServiceQueue \in AwaiterListType
    /\  ResourceOwner \in AwaiterListType
    /\  ServiceQueueOwner \in AwaiterListType
    /\  AcquiredLocks \in [ Threads -> { "Unlocked", "Pending", "Read", "Write", "Released" }]

(* --algorithm ReaderWriterLock

variables
    ReaderCount = 0,
    ReaderCountWaiters = << >>,
    ReaderCountOwner = << >>,
    ResourceWaiters = << >>,
    ResourceOwner = << >>,
    ServiceQueue = << >>,
    ServiceQueueOwner = << >>,
    AcquiredLocks = [ thread \in Threads |-> "Unlocked" ];

macro EnqueueForOwnership(queue, queueOwner)
begin
    if queueOwner = << >> then
        queueOwner := << self >>;
    else
        queue := queue \o << self >>;
    end if;
end macro;

macro ReleaseOwnership(queue, queueOwner)
begin
    if queue = << >> then
        queueOwner := << >>;
    else
        queueOwner := << Head(queue) >>;
        queue := Tail(queue);
    end if;
end macro;

fair process Worker \in Threads
begin
Start:
    AcquiredLocks[self] := "Pending";
    \* All requests start by entering the service queue.
    EnqueueForOwnership(ServiceQueue, ServiceQueueOwner);

WaitForServiceQueueOwnership:
    await ServiceQueueOwner = << self >>;

    \* Now we decide to either be a reader or a writer
    either
        \* Let's be a reader!
        EnqueueForOwnership(ReaderCountWaiters, ReaderCountOwner);
AcquireRead_WaitForReaderCountOwnership:
        await ReaderCountOwner = << self >>;

        ReaderCount := ReaderCount + 1;
        if ReaderCount = 1 then
            EnqueueForOwnership(ResourceWaiters, ResourceOwner);
AcquireRead_WaitForResourceOwnership:
            await ResourceOwner = << self >>;
            ReleaseOwnership(ServiceQueue, ServiceQueueOwner);
        else
            ReleaseOwnership(ServiceQueue, ServiceQueueOwner);
        end if;

AcquireRead_ReleaseReaderCountOwnership:
        ReleaseOwnership(ReaderCountWaiters, ReaderCountOwner);
        AcquiredLocks[self] := "Read";

ReleaseRead_AcquireReaderCountOwnership:
        AcquiredLocks[self] := "Released";
        EnqueueForOwnership(ReaderCountWaiters, ReaderCountOwner);

ReleaseRead_WaitForReaderCountOwnership:
        await ReaderCountOwner = << self >>;

        ReaderCount := ReaderCount - 1;
        if ReaderCount = 0 then
            ReleaseOwnership(ResourceWaiters, ResourceOwner);
        end if;
ReleaseRead_ReleaseReaderCountOwnership:
        ReleaseOwnership(ReaderCountWaiters, ReaderCountOwner);
        
        \* All done with the read path!
    or
        \* Let's be a writer!
AcquireWrite_AddToResourceQueue:
        EnqueueForOwnership(ResourceWaiters, ResourceOwner);
AcquireWrite_WaitForResourceOwnership:
        await ResourceOwner = << self >>;

AcquireWrite_ReleaseServiceQueue:
        ReleaseOwnership(ServiceQueue, ServiceQueueOwner);
        AcquiredLocks[self] := "Write";
   
AcquireWrite_ReleaseResourceOwnership:
        ReleaseOwnership(ResourceWaiters, ResourceOwner);
        AcquiredLocks[self] := "Released";
        \* All done with the write path!
    end either;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "7bf39b9f" /\ chksum(tla) = "6c1bce44")
VARIABLES ReaderCount, ReaderCountWaiters, ReaderCountOwner, ResourceWaiters, 
          ResourceOwner, ServiceQueue, ServiceQueueOwner, AcquiredLocks, pc

vars == << ReaderCount, ReaderCountWaiters, ReaderCountOwner, ResourceWaiters, 
           ResourceOwner, ServiceQueue, ServiceQueueOwner, AcquiredLocks, pc
        >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ ReaderCount = 0
        /\ ReaderCountWaiters = << >>
        /\ ReaderCountOwner = << >>
        /\ ResourceWaiters = << >>
        /\ ResourceOwner = << >>
        /\ ServiceQueue = << >>
        /\ ServiceQueueOwner = << >>
        /\ AcquiredLocks = [ thread \in Threads |-> "Unlocked" ]
        /\ pc = [self \in ProcSet |-> "Start"]

Start(self) == /\ pc[self] = "Start"
               /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Pending"]
               /\ IF ServiceQueueOwner = << >>
                     THEN /\ ServiceQueueOwner' = << self >>
                          /\ UNCHANGED ServiceQueue
                     ELSE /\ ServiceQueue' = ServiceQueue \o << self >>
                          /\ UNCHANGED ServiceQueueOwner
               /\ pc' = [pc EXCEPT ![self] = "WaitForServiceQueueOwnership"]
               /\ UNCHANGED << ReaderCount, ReaderCountWaiters, 
                               ReaderCountOwner, ResourceWaiters, 
                               ResourceOwner >>

WaitForServiceQueueOwnership(self) == /\ pc[self] = "WaitForServiceQueueOwnership"
                                      /\ ServiceQueueOwner = << self >>
                                      /\ \/ /\ IF ReaderCountOwner = << >>
                                                  THEN /\ ReaderCountOwner' = << self >>
                                                       /\ UNCHANGED ReaderCountWaiters
                                                  ELSE /\ ReaderCountWaiters' = ReaderCountWaiters \o << self >>
                                                       /\ UNCHANGED ReaderCountOwner
                                            /\ pc' = [pc EXCEPT ![self] = "AcquireRead_WaitForReaderCountOwnership"]
                                         \/ /\ pc' = [pc EXCEPT ![self] = "AcquireWrite_AddToResourceQueue"]
                                            /\ UNCHANGED <<ReaderCountWaiters, ReaderCountOwner>>
                                      /\ UNCHANGED << ReaderCount, 
                                                      ResourceWaiters, 
                                                      ResourceOwner, 
                                                      ServiceQueue, 
                                                      ServiceQueueOwner, 
                                                      AcquiredLocks >>

AcquireRead_WaitForReaderCountOwnership(self) == /\ pc[self] = "AcquireRead_WaitForReaderCountOwnership"
                                                 /\ ReaderCountOwner = << self >>
                                                 /\ ReaderCount' = ReaderCount + 1
                                                 /\ IF ReaderCount' = 1
                                                       THEN /\ IF ResourceOwner = << >>
                                                                  THEN /\ ResourceOwner' = << self >>
                                                                       /\ UNCHANGED ResourceWaiters
                                                                  ELSE /\ ResourceWaiters' = ResourceWaiters \o << self >>
                                                                       /\ UNCHANGED ResourceOwner
                                                            /\ pc' = [pc EXCEPT ![self] = "AcquireRead_WaitForResourceOwnership"]
                                                            /\ UNCHANGED << ServiceQueue, 
                                                                            ServiceQueueOwner >>
                                                       ELSE /\ IF ServiceQueue = << >>
                                                                  THEN /\ ServiceQueueOwner' = << >>
                                                                       /\ UNCHANGED ServiceQueue
                                                                  ELSE /\ ServiceQueueOwner' = << Head(ServiceQueue) >>
                                                                       /\ ServiceQueue' = Tail(ServiceQueue)
                                                            /\ pc' = [pc EXCEPT ![self] = "AcquireRead_ReleaseReaderCountOwnership"]
                                                            /\ UNCHANGED << ResourceWaiters, 
                                                                            ResourceOwner >>
                                                 /\ UNCHANGED << ReaderCountWaiters, 
                                                                 ReaderCountOwner, 
                                                                 AcquiredLocks >>

AcquireRead_WaitForResourceOwnership(self) == /\ pc[self] = "AcquireRead_WaitForResourceOwnership"
                                              /\ ResourceOwner = << self >>
                                              /\ IF ServiceQueue = << >>
                                                    THEN /\ ServiceQueueOwner' = << >>
                                                         /\ UNCHANGED ServiceQueue
                                                    ELSE /\ ServiceQueueOwner' = << Head(ServiceQueue) >>
                                                         /\ ServiceQueue' = Tail(ServiceQueue)
                                              /\ pc' = [pc EXCEPT ![self] = "AcquireRead_ReleaseReaderCountOwnership"]
                                              /\ UNCHANGED << ReaderCount, 
                                                              ReaderCountWaiters, 
                                                              ReaderCountOwner, 
                                                              ResourceWaiters, 
                                                              ResourceOwner, 
                                                              AcquiredLocks >>

AcquireRead_ReleaseReaderCountOwnership(self) == /\ pc[self] = "AcquireRead_ReleaseReaderCountOwnership"
                                                 /\ IF ReaderCountWaiters = << >>
                                                       THEN /\ ReaderCountOwner' = << >>
                                                            /\ UNCHANGED ReaderCountWaiters
                                                       ELSE /\ ReaderCountOwner' = << Head(ReaderCountWaiters) >>
                                                            /\ ReaderCountWaiters' = Tail(ReaderCountWaiters)
                                                 /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Read"]
                                                 /\ pc' = [pc EXCEPT ![self] = "ReleaseRead_AcquireReaderCountOwnership"]
                                                 /\ UNCHANGED << ReaderCount, 
                                                                 ResourceWaiters, 
                                                                 ResourceOwner, 
                                                                 ServiceQueue, 
                                                                 ServiceQueueOwner >>

ReleaseRead_AcquireReaderCountOwnership(self) == /\ pc[self] = "ReleaseRead_AcquireReaderCountOwnership"
                                                 /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Released"]
                                                 /\ IF ReaderCountOwner = << >>
                                                       THEN /\ ReaderCountOwner' = << self >>
                                                            /\ UNCHANGED ReaderCountWaiters
                                                       ELSE /\ ReaderCountWaiters' = ReaderCountWaiters \o << self >>
                                                            /\ UNCHANGED ReaderCountOwner
                                                 /\ pc' = [pc EXCEPT ![self] = "ReleaseRead_WaitForReaderCountOwnership"]
                                                 /\ UNCHANGED << ReaderCount, 
                                                                 ResourceWaiters, 
                                                                 ResourceOwner, 
                                                                 ServiceQueue, 
                                                                 ServiceQueueOwner >>

ReleaseRead_WaitForReaderCountOwnership(self) == /\ pc[self] = "ReleaseRead_WaitForReaderCountOwnership"
                                                 /\ ReaderCountOwner = << self >>
                                                 /\ ReaderCount' = ReaderCount - 1
                                                 /\ IF ReaderCount' = 0
                                                       THEN /\ IF ResourceWaiters = << >>
                                                                  THEN /\ ResourceOwner' = << >>
                                                                       /\ UNCHANGED ResourceWaiters
                                                                  ELSE /\ ResourceOwner' = << Head(ResourceWaiters) >>
                                                                       /\ ResourceWaiters' = Tail(ResourceWaiters)
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << ResourceWaiters, 
                                                                            ResourceOwner >>
                                                 /\ pc' = [pc EXCEPT ![self] = "ReleaseRead_ReleaseReaderCountOwnership"]
                                                 /\ UNCHANGED << ReaderCountWaiters, 
                                                                 ReaderCountOwner, 
                                                                 ServiceQueue, 
                                                                 ServiceQueueOwner, 
                                                                 AcquiredLocks >>

ReleaseRead_ReleaseReaderCountOwnership(self) == /\ pc[self] = "ReleaseRead_ReleaseReaderCountOwnership"
                                                 /\ IF ReaderCountWaiters = << >>
                                                       THEN /\ ReaderCountOwner' = << >>
                                                            /\ UNCHANGED ReaderCountWaiters
                                                       ELSE /\ ReaderCountOwner' = << Head(ReaderCountWaiters) >>
                                                            /\ ReaderCountWaiters' = Tail(ReaderCountWaiters)
                                                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                 /\ UNCHANGED << ReaderCount, 
                                                                 ResourceWaiters, 
                                                                 ResourceOwner, 
                                                                 ServiceQueue, 
                                                                 ServiceQueueOwner, 
                                                                 AcquiredLocks >>

AcquireWrite_AddToResourceQueue(self) == /\ pc[self] = "AcquireWrite_AddToResourceQueue"
                                         /\ IF ResourceOwner = << >>
                                               THEN /\ ResourceOwner' = << self >>
                                                    /\ UNCHANGED ResourceWaiters
                                               ELSE /\ ResourceWaiters' = ResourceWaiters \o << self >>
                                                    /\ UNCHANGED ResourceOwner
                                         /\ pc' = [pc EXCEPT ![self] = "AcquireWrite_WaitForResourceOwnership"]
                                         /\ UNCHANGED << ReaderCount, 
                                                         ReaderCountWaiters, 
                                                         ReaderCountOwner, 
                                                         ServiceQueue, 
                                                         ServiceQueueOwner, 
                                                         AcquiredLocks >>

AcquireWrite_WaitForResourceOwnership(self) == /\ pc[self] = "AcquireWrite_WaitForResourceOwnership"
                                               /\ ResourceOwner = << self >>
                                               /\ pc' = [pc EXCEPT ![self] = "AcquireWrite_ReleaseServiceQueue"]
                                               /\ UNCHANGED << ReaderCount, 
                                                               ReaderCountWaiters, 
                                                               ReaderCountOwner, 
                                                               ResourceWaiters, 
                                                               ResourceOwner, 
                                                               ServiceQueue, 
                                                               ServiceQueueOwner, 
                                                               AcquiredLocks >>

AcquireWrite_ReleaseServiceQueue(self) == /\ pc[self] = "AcquireWrite_ReleaseServiceQueue"
                                          /\ IF ServiceQueue = << >>
                                                THEN /\ ServiceQueueOwner' = << >>
                                                     /\ UNCHANGED ServiceQueue
                                                ELSE /\ ServiceQueueOwner' = << Head(ServiceQueue) >>
                                                     /\ ServiceQueue' = Tail(ServiceQueue)
                                          /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Write"]
                                          /\ pc' = [pc EXCEPT ![self] = "AcquireWrite_ReleaseResourceOwnership"]
                                          /\ UNCHANGED << ReaderCount, 
                                                          ReaderCountWaiters, 
                                                          ReaderCountOwner, 
                                                          ResourceWaiters, 
                                                          ResourceOwner >>

AcquireWrite_ReleaseResourceOwnership(self) == /\ pc[self] = "AcquireWrite_ReleaseResourceOwnership"
                                               /\ IF ResourceWaiters = << >>
                                                     THEN /\ ResourceOwner' = << >>
                                                          /\ UNCHANGED ResourceWaiters
                                                     ELSE /\ ResourceOwner' = << Head(ResourceWaiters) >>
                                                          /\ ResourceWaiters' = Tail(ResourceWaiters)
                                               /\ AcquiredLocks' = [AcquiredLocks EXCEPT ![self] = "Released"]
                                               /\ pc' = [pc EXCEPT ![self] = "Done"]
                                               /\ UNCHANGED << ReaderCount, 
                                                               ReaderCountWaiters, 
                                                               ReaderCountOwner, 
                                                               ServiceQueue, 
                                                               ServiceQueueOwner >>

Worker(self) == Start(self) \/ WaitForServiceQueueOwnership(self)
                   \/ AcquireRead_WaitForReaderCountOwnership(self)
                   \/ AcquireRead_WaitForResourceOwnership(self)
                   \/ AcquireRead_ReleaseReaderCountOwnership(self)
                   \/ ReleaseRead_AcquireReaderCountOwnership(self)
                   \/ ReleaseRead_WaitForReaderCountOwnership(self)
                   \/ ReleaseRead_ReleaseReaderCountOwnership(self)
                   \/ AcquireWrite_AddToResourceQueue(self)
                   \/ AcquireWrite_WaitForResourceOwnership(self)
                   \/ AcquireWrite_ReleaseServiceQueue(self)
                   \/ AcquireWrite_ReleaseResourceOwnership(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: Worker(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Threads : WF_vars(Worker(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Symmetry == Permutations(Threads)

AllLocksAreCompatible ==
    \/  /\  \A thread \in Threads : AcquiredLocks[thread] # "Write"
    \/  /\  \A thread1, thread2 \in Threads : 
            /\  AcquiredLocks[thread1] # "Read"
            /\  (
                    /\  AcquiredLocks[thread1] = "Write"
                    /\  AcquiredLocks[thread2] = "Write"
                ) => (thread1 = thread2)

LocksServicedInOrder ==
    [](
        \A thread1, thread2 \in Threads :
            (
                /\  thread1 # thread2
                /\  AcquiredLocks[thread1] = "Unlocked"
                /\  AcquiredLocks[thread2] = "Pending"
            ) ~> (
                /\  AcquiredLocks[thread1] # "Released"
                /\  AcquiredLocks[thread2] \in { "Read", "Write" }
            )
    )

==== 
