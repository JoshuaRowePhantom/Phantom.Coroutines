---- MODULE ReadCopyUpdate_MemorySafety ----
EXTENDS FiniteSets, TLC, Integers

CONSTANT SectionCount, OperationCount, ThreadCount
VARIABLE Sections, Threads, Operations


EmptyId == [ Empty |-> TRUE ]
EmptyValue == [ Section |-> EmptyId, Operation |-> EmptyId ]

SectionId == [ SectionId : 1..SectionCount ]
OperationId == [ Operation : 1..OperationCount ]
ThreadId == [ Thread : 1..ThreadCount ]

EmptyReference == 
    [
        SoftReference |-> EmptyValue,
        HardReference |-> EmptyValue
    ]

EmptyOperation ==
    [
        Section |-> EmptyId,
        Thread |-> EmptyId,
        Reference |-> EmptyReference
    ]

ValueType == [ 
    Section : SectionId \union { EmptyId },
    Operation : OperationId \union { EmptyId }
]

ReferenceType == 
    {
        reference \in
        [
            SoftReference : ValueType,
            HardReference : ValueType
        ]
        :
        \/  reference.HardReference = EmptyValue
        \/  reference.HardReference = reference.SoftReference
    }

SectionType ==
    [
        Complete : BOOLEAN,
        Reference : ReferenceType
    ]

OperationType ==
    [
        Section : SectionId \union {EmptyId},
        Thread : ThreadId \union {EmptyId},
        Reference : ReferenceType
    ]

ThreadType ==
    [
        Reference : ReferenceType
    ]

AllReferences ==
    { Sections[sectionId].Reference : sectionId \in SectionId }
    \union
    { Threads[threadId].Reference : threadId \in ThreadId }
    \union 
    { Operations[operationId].Reference : operationId \in OperationId }

ReferenceCount(value) ==
    Cardinality({ reference \in AllReferences : reference.HardReference = value })

SectionHardReferences(sectionId) ==
    { reference \in AllReferences : reference.HardReference.Section = sectionId }

ThreadOperationIdsForCurrentSoftReference(threadId) ==
    { 
        operationId \in OperationId :
            /\  Operations[operationId].Thread = threadId
            /\  Operations[operationId].Reference.SoftReference = Threads[threadId].Reference.SoftReference 
    }

ThreadIdsUsingSectionSoftReference(sectionId) ==
    {
        threadId \in ThreadId :
            /\  Sections[sectionId].Reference.SoftReference # EmptyValue
            /\  Threads[threadId].Reference.SoftReference = Sections[sectionId].Reference.SoftReference
    }

CanRead(value) ==
    \/  /\  value = EmptyValue
    \/  /\  value \in ValueType
        /\  ReferenceCount(value) > 0
        /\  Sections[value.Section].Complete = FALSE

(* --algorithm ReadCopyUpdate_MemorySafety 

variables
    Sections = 
    [ 
        sectionId \in SectionId |->
        [
            Complete |-> FALSE,
            Reference |-> EmptyReference 
        ]
    ],
    Operations = 
    [ 
        operationId \in OperationId |-> EmptyOperation
    ],
    Threads = [ threadId \in ThreadId |-> [ Reference |-> EmptyReference ]];

macro DetectThreadCanComplete()
begin
    \* The thread is allowed to stop when all its operations are complete.
    await \A operationId \in OperationId :
        \/  Operations[operationId].Thread # self;
end macro;

macro StartOperation(operationId, sectionId)
begin
    await Operations[operationId].Thread = EmptyId;
    await Sections[sectionId].Complete = FALSE;

    Operations[operationId] :=
    [
        Section |-> sectionId,
        Thread |-> self,
        Reference |-> EmptyReference
    ];
end macro;

macro EndOperation(operationId)
begin
    Operations[operationId] := EmptyOperation;
end macro;

process section \in SectionId
begin
SectionDestructor:
    \* The section is allowed to be destroyed when all its operations are complete.
    await \A operationId \in OperationId : 
        \/  Operations[operationId].Section # self;

    Sections[self].Complete := TRUE;

SectionRemoveThreadReferences:
    while {} # ThreadIdsUsingSectionSoftReference(self) do
        with threadId \in ThreadIdsUsingSectionSoftReference(self) do
            Threads[threadId].Reference := EmptyReference;
        end with;
    end while;
    Sections[self].Reference := EmptyReference;
    
SectionEnd:
    assert Cardinality(SectionHardReferences(self)) = 0;
end process;

process thread \in ThreadId
variables 
    ThreadOperationId = EmptyId
begin
ThreadLoop:
    either
        with operationId \in OperationId,
            sectionId \in SectionId
        do
            ThreadOperationId := operationId;
            StartOperation(operationId, sectionId);
            goto ThreadRefreshOperation;
        end with;
    or
        with operationId \in OperationId
        do
            await Operations[operationId].Thread = self;
            either
                ThreadOperationId := operationId;
                goto ThreadRefreshOperation;
            or
                ThreadOperationId := operationId;
                goto ThreadWriteOperation;
            or
                assert CanRead(Operations[operationId].Reference.SoftReference);
                goto ThreadLoop;
            or
                EndOperation(operationId);
                goto ThreadLoop;
            end either;
        end with;
    or
        DetectThreadCanComplete();
        goto ThreadEnd;
    end either;

ThreadRefreshOperation:
    if Threads[self].Reference.SoftReference # Sections[Operations[ThreadOperationId].Section].Reference.SoftReference then
        \* Must refresh the thread-local value.

        \* For every operation on the current thread using the current hard reference,
        \* update the operation to use a hard reference.
ThreadRefreshConvertOperationToHardReference:
        while {} # ThreadOperationIdsForCurrentSoftReference(self)
        do
            with operationId \in ThreadOperationIdsForCurrentSoftReference(self) do
                Operations[operationId].Reference.HardReference := Threads[self].Reference.HardReference;
            end with;
        end while;

ThreadRefreshUpdateThreadLocal:
        Threads[self].Reference := Sections[Operations[ThreadOperationId].Section].Reference;
    end if;

ThreadRefreshUpdateOperation:
    Operations[ThreadOperationId].Reference :=
    [
        HardReference |-> EmptyValue,
        SoftReference |-> Threads[self].Reference.SoftReference
    ];

    ThreadOperationId := EmptyId;
    goto ThreadLoop;

ThreadWriteOperation:
    with value = [
        Section |-> Operations[ThreadOperationId].Section,
        Operation |-> ThreadOperationId
    ] do
        Operations[ThreadOperationId].Reference :=
        [
            HardReference |-> value,
            SoftReference |-> value
        ];
    end with;

ThreadWriteUpdateSection:
    Sections[Operations[ThreadOperationId].Section].Reference := Operations[ThreadOperationId].Reference;
    ThreadOperationId := EmptyId;
    goto ThreadLoop;

ThreadEnd:
    skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b96a82a1" /\ chksum(tla) = "ae3f1f07")
VARIABLES Sections, Operations, Threads, pc, ThreadOperationId

vars == << Sections, Operations, Threads, pc, ThreadOperationId >>

ProcSet == (SectionId) \cup (ThreadId)

Init == (* Global variables *)
        /\ Sections = [
                          sectionId \in SectionId |->
                          [
                              Complete |-> FALSE,
                              Reference |-> EmptyReference
                          ]
                      ]
        /\ Operations = [
                            operationId \in OperationId |-> EmptyOperation
                        ]
        /\ Threads = [ threadId \in ThreadId |-> [ Reference |-> EmptyReference ]]
        (* Process thread *)
        /\ ThreadOperationId = [self \in ThreadId |-> EmptyId]
        /\ pc = [self \in ProcSet |-> CASE self \in SectionId -> "SectionDestructor"
                                        [] self \in ThreadId -> "ThreadLoop"]

SectionDestructor(self) == /\ pc[self] = "SectionDestructor"
                           /\   \A operationId \in OperationId :
                              \/  Operations[operationId].Section # self
                           /\ Sections' = [Sections EXCEPT ![self].Complete = TRUE]
                           /\ pc' = [pc EXCEPT ![self] = "SectionRemoveThreadReferences"]
                           /\ UNCHANGED << Operations, Threads, 
                                           ThreadOperationId >>

SectionRemoveThreadReferences(self) == /\ pc[self] = "SectionRemoveThreadReferences"
                                       /\ IF {} # ThreadIdsUsingSectionSoftReference(self)
                                             THEN /\ \E threadId \in ThreadIdsUsingSectionSoftReference(self):
                                                       Threads' = [Threads EXCEPT ![threadId].Reference = EmptyReference]
                                                  /\ pc' = [pc EXCEPT ![self] = "SectionRemoveThreadReferences"]
                                                  /\ UNCHANGED Sections
                                             ELSE /\ Sections' = [Sections EXCEPT ![self].Reference = EmptyReference]
                                                  /\ pc' = [pc EXCEPT ![self] = "SectionEnd"]
                                                  /\ UNCHANGED Threads
                                       /\ UNCHANGED << Operations, 
                                                       ThreadOperationId >>

SectionEnd(self) == /\ pc[self] = "SectionEnd"
                    /\ Assert(Cardinality(SectionHardReferences(self)) = 0, 
                              "Failure of assertion at line 156, column 5.")
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << Sections, Operations, Threads, 
                                    ThreadOperationId >>

section(self) == SectionDestructor(self)
                    \/ SectionRemoveThreadReferences(self)
                    \/ SectionEnd(self)

ThreadLoop(self) == /\ pc[self] = "ThreadLoop"
                    /\ \/ /\ \E operationId \in OperationId:
                               \E sectionId \in SectionId:
                                 /\ ThreadOperationId' = [ThreadOperationId EXCEPT ![self] = operationId]
                                 /\ Operations[operationId].Thread = EmptyId
                                 /\ Sections[sectionId].Complete = FALSE
                                 /\ Operations' = [Operations EXCEPT ![operationId] = [
                                                                                          Section |-> sectionId,
                                                                                          Thread |-> self,
                                                                                          Reference |-> EmptyReference
                                                                                      ]]
                                 /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshOperation"]
                       \/ /\ \E operationId \in OperationId:
                               /\ Operations[operationId].Thread = self
                               /\ \/ /\ ThreadOperationId' = [ThreadOperationId EXCEPT ![self] = operationId]
                                     /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshOperation"]
                                     /\ UNCHANGED Operations
                                  \/ /\ ThreadOperationId' = [ThreadOperationId EXCEPT ![self] = operationId]
                                     /\ pc' = [pc EXCEPT ![self] = "ThreadWriteOperation"]
                                     /\ UNCHANGED Operations
                                  \/ /\ Assert(CanRead(Operations[operationId].Reference.SoftReference), 
                                               "Failure of assertion at line 183, column 17.")
                                     /\ pc' = [pc EXCEPT ![self] = "ThreadLoop"]
                                     /\ UNCHANGED <<Operations, ThreadOperationId>>
                                  \/ /\ Operations' = [Operations EXCEPT ![operationId] = EmptyOperation]
                                     /\ pc' = [pc EXCEPT ![self] = "ThreadLoop"]
                                     /\ UNCHANGED ThreadOperationId
                       \/ /\   \A operationId \in OperationId :
                             \/  Operations[operationId].Thread # self
                          /\ pc' = [pc EXCEPT ![self] = "ThreadEnd"]
                          /\ UNCHANGED <<Operations, ThreadOperationId>>
                    /\ UNCHANGED << Sections, Threads >>

ThreadRefreshOperation(self) == /\ pc[self] = "ThreadRefreshOperation"
                                /\ IF Threads[self].Reference.SoftReference # Sections[Operations[ThreadOperationId[self]].Section].Reference.SoftReference
                                      THEN /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshConvertOperationToHardReference"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshUpdateOperation"]
                                /\ UNCHANGED << Sections, Operations, Threads, 
                                                ThreadOperationId >>

ThreadRefreshConvertOperationToHardReference(self) == /\ pc[self] = "ThreadRefreshConvertOperationToHardReference"
                                                      /\ IF {} # ThreadOperationIdsForCurrentSoftReference(self)
                                                            THEN /\ \E operationId \in ThreadOperationIdsForCurrentSoftReference(self):
                                                                      Operations' = [Operations EXCEPT ![operationId].Reference.HardReference = Threads[self].Reference.HardReference]
                                                                 /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshConvertOperationToHardReference"]
                                                            ELSE /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshUpdateThreadLocal"]
                                                                 /\ UNCHANGED Operations
                                                      /\ UNCHANGED << Sections, 
                                                                      Threads, 
                                                                      ThreadOperationId >>

ThreadRefreshUpdateThreadLocal(self) == /\ pc[self] = "ThreadRefreshUpdateThreadLocal"
                                        /\ Threads' = [Threads EXCEPT ![self].Reference = Sections[Operations[ThreadOperationId[self]].Section].Reference]
                                        /\ pc' = [pc EXCEPT ![self] = "ThreadRefreshUpdateOperation"]
                                        /\ UNCHANGED << Sections, Operations, 
                                                        ThreadOperationId >>

ThreadRefreshUpdateOperation(self) == /\ pc[self] = "ThreadRefreshUpdateOperation"
                                      /\ Operations' = [Operations EXCEPT ![ThreadOperationId[self]].Reference = [
                                                                                                                     HardReference |-> EmptyValue,
                                                                                                                     SoftReference |-> Threads[self].Reference.SoftReference
                                                                                                                 ]]
                                      /\ ThreadOperationId' = [ThreadOperationId EXCEPT ![self] = EmptyId]
                                      /\ pc' = [pc EXCEPT ![self] = "ThreadLoop"]
                                      /\ UNCHANGED << Sections, Threads >>

ThreadWriteOperation(self) == /\ pc[self] = "ThreadWriteOperation"
                              /\ LET value ==              [
                                                  Section |-> Operations[ThreadOperationId[self]].Section,
                                                  Operation |-> ThreadOperationId[self]
                                              ] IN
                                   Operations' = [Operations EXCEPT ![ThreadOperationId[self]].Reference = [
                                                                                                               HardReference |-> value,
                                                                                                               SoftReference |-> value
                                                                                                           ]]
                              /\ pc' = [pc EXCEPT ![self] = "ThreadWriteUpdateSection"]
                              /\ UNCHANGED << Sections, Threads, 
                                              ThreadOperationId >>

ThreadWriteUpdateSection(self) == /\ pc[self] = "ThreadWriteUpdateSection"
                                  /\ Sections' = [Sections EXCEPT ![Operations[ThreadOperationId[self]].Section].Reference = Operations[ThreadOperationId[self]].Reference]
                                  /\ ThreadOperationId' = [ThreadOperationId EXCEPT ![self] = EmptyId]
                                  /\ pc' = [pc EXCEPT ![self] = "ThreadLoop"]
                                  /\ UNCHANGED << Operations, Threads >>

ThreadEnd(self) == /\ pc[self] = "ThreadEnd"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << Sections, Operations, Threads, 
                                   ThreadOperationId >>

thread(self) == ThreadLoop(self) \/ ThreadRefreshOperation(self)
                   \/ ThreadRefreshConvertOperationToHardReference(self)
                   \/ ThreadRefreshUpdateThreadLocal(self)
                   \/ ThreadRefreshUpdateOperation(self)
                   \/ ThreadWriteOperation(self)
                   \/ ThreadWriteUpdateSection(self) \/ ThreadEnd(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in SectionId: section(self))
           \/ (\E self \in ThreadId: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TypeOk ==
    /\  Sections \in [SectionId -> SectionType]
    /\  Operations \in [OperationId -> OperationType]
    /\  Threads \in [ThreadId -> ThreadType]

====
