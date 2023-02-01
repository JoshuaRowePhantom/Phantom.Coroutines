---- MODULE FairReaderWriterLock ----
(* 
A ReaderWriterLock that guarantees that all readers or writers
queued are serviced before other readers or writers.
*)

EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANT Threads
VARIABLE
    Queue,
    Locks,
    Destroyed

vars == <<
    Queue,
    Locks,
    Destroyed
>>

AbstractLock == INSTANCE AbstractReaderWriterLock

LockType == AbstractLock!LockType
QueueAsSet(queue) == { queue[i] : i \in DOMAIN queue }
QueueType == Seq(LockType)

ReadLock(thread) == [ Type |-> "Read", Thread |-> thread ]
WriteLock(thread) == [ Type |-> "Write", Thread |-> thread ]

TypeOk ==
    /\  Queue \in QueueType
    /\  Locks \in SUBSET LockType
    /\  Destroyed \in BOOLEAN

Invariant ==
    /\  TypeOk
    /\  AbstractLock!TypeOk
    /\  AbstractLock!LocksAreCompatible

Init ==
    /\  Queue = << >>
    /\  Locks = { }
    /\  Destroyed = FALSE

IsNotLocked(thread) ==
    /\  ~ \E lock \in Locks : lock.Thread = thread

IsNotQueued(thread) ==
    /\  ~ \E i \in DOMAIN Queue : Queue[i].Thread = thread

QueueRead(thread) ==
    /\  ~Destroyed
    /\  IsNotLocked(thread)
    /\  IsNotQueued(thread)
    /\  Queue' = Queue \o << ReadLock(thread) >>
    /\  UNCHANGED Locks
    /\  UNCHANGED Destroyed
    
QueueWrite(thread) ==
    /\  ~Destroyed
    /\  IsNotLocked(thread)
    /\  IsNotQueued(thread)
    /\  Queue' = Queue \o << WriteLock(thread) >>
    /\  UNCHANGED Locks
    /\  UNCHANGED Destroyed

LockRead(thread) ==
    /\  ~Destroyed
    /\  Queue # << >>
    /\  Head(Queue) = ReadLock(thread)
    /\  Queue' = Tail(Queue)
    /\  \A lock \in Locks : lock.Type = "Read"
    /\  Locks' = Locks \union { ReadLock(thread) }
    /\  UNCHANGED Destroyed

LockWrite(thread) ==
    /\  ~Destroyed
    /\  Queue # << >>
    /\  Head(Queue) = WriteLock(thread)
    /\  Queue' = Tail(Queue)
    /\  Locks = { }
    /\  Locks' = Locks \union { WriteLock(thread) }
    /\  UNCHANGED Destroyed

LockReadFast(thread) ==
    /\  ~Destroyed
    /\  \/  /\  Queue = << >>
            /\  IsNotLocked(thread)
            /\  UNCHANGED Queue
    /\  \A lock \in Locks : lock.Type = "Read"
    /\  Locks' = Locks \union { ReadLock(thread) }
    /\  UNCHANGED Destroyed

LockWriteFast(thread) ==
    /\  ~Destroyed
    /\  \/  /\  Queue = << >>
            /\  IsNotLocked(thread)
            /\  UNCHANGED Queue
    /\  Locks = { }
    /\  Locks' = Locks \union { WriteLock(thread) }
    /\  UNCHANGED Destroyed

Unlock(thread) ==
    /\  ~Destroyed
    /\  \E lock \in Locks :
        /\  lock.Thread = thread
        /\  Locks' = Locks \ { lock }
    /\  UNCHANGED Queue
    /\  UNCHANGED Destroyed

Destroy ==
    /\  Locks = { }
    /\  Queue = << >>
    /\  Destroyed' = TRUE
    /\  UNCHANGED << Locks, Queue >>

Next ==
    \E thread \in Threads :
    \/  LockReadFast(thread)
    \/  LockWriteFast(thread)
    \/  QueueRead(thread)
    \/  QueueWrite(thread)
    \/  LockRead(thread)
    \/  LockWrite(thread)
    \/  Unlock(thread)
    \/  Destroy

Fairness ==
    /\  \A thread \in Threads :
        /\  WF_vars(QueueRead(thread))
        /\  WF_vars(QueueWrite(thread))
        /\  WF_vars(LockReadFast(thread))
        /\  WF_vars(LockWriteFast(thread))
        /\  WF_vars(LockRead(thread))
        /\  WF_vars(LockWrite(thread))
        /\  WF_vars(Unlock(thread))
        /\  WF_vars(Destroy)

Spec ==
    /\  Init
    /\  [][Next]_vars
    /\  Fairness
    
Property ==
    /\  Spec
    /\  []AbstractLock!TypeOk
    /\  []TypeOk

Alias == [
    Locks |-> Locks,
    Queue |-> Queue,
    Threads |-> [
        thread \in Threads |->
        [
            LockReadFastEnabled |-> ENABLED(LockReadFast(thread)),
            LockWriteFastEnabled |-> ENABLED(LockWriteFast(thread)),
            QueueReadEnabled |-> ENABLED(QueueRead(thread)),
            QueueWriteEnabled |-> ENABLED(QueueWrite(thread)),
            LockReadEnabled |-> ENABLED(LockRead(thread)),
            LockWriteEnabled |-> ENABLED(LockWrite(thread)),
            UnlockEnabled |-> ENABLED(Unlock(thread)),
            IsNotLocked |-> IsNotLocked(thread),
            IsNotQueued |-> IsNotQueued(thread)
        ]
    ],
    DestroyEnabled |-> ENABLED(Destroy),
    Destroyed |-> Destroyed
]
====
