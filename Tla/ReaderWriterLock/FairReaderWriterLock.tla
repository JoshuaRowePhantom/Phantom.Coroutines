---- MODULE FairReaderWriterLock ----
(* 
A ReaderWriterLock that guarantees that all readers or writers
queued are serviced before other readers or writers.
*)

EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANT Threads
VARIABLE
    Queue,
    Locks

vars == <<
    Queue,
    Locks
>>

AbstractLock == INSTANCE AbstractReaderWriterLock

LockType == AbstractLock!LockType
QueueAsSet(queue) == { queue[i] : i \in DOMAIN queue }
QueueType == { queue \in UNION { 
    [1..length -> LockType] : length \in 0..Cardinality(Threads)
}
:
\A i, j \in 1..Len(queue) :
    \/  queue[i].Thread # queue[j].Thread
    \/  i = j
}

TypeOk ==
    /\  Queue \in QueueType
    /\  Locks \in SUBSET LockType

Invariant ==
    /\  TypeOk
    /\  AbstractLock!TypeOk
    /\  AbstractLock!LocksAreCompatible

Init ==
    /\  Queue = << >>
    /\  Locks = { }

Next ==
    /\  Locks' \in SUBSET LockType
    /\  AbstractLock!LocksAreCompatible'
    /\  Queue' \in QueueType
    
    \* The new queue must not have any prexisting locks in it.
    /\  QueueAsSet(Queue') \intersect Locks' = { }
    
    \* Some prefix of the queue must have been put into the set of locks
    /\  \E i \in 0..Len(Queue) :
        \A j \in 1..i :
            /\  Queue[j] \in Locks'

        /\  \A lock \in Locks' :
            \* Any lock that was already in Lock is allowed to remain.
            \/  lock \in Locks

            \* Or the new queue is empty, meaning that it was serviced completely really really fast
            \/  Queue' = << >>

            \* Or it is in the prefix placed in the queue.
            \/  \E k \in 1..i :
                Queue[k] = lock

Spec ==
    /\  Init
    /\  [][Next]_vars

Property ==
    /\  []AbstractLock!TypeOk
    /\  []TypeOk

====
