---- MODULE AbstractReaderWriterLock ----
EXTENDS FiniteSets, Integers

CONSTANT Threads

VARIABLE 
    Locks

vars == <<
    Locks
>>

LockType == [
    Type : { "Read", "Write" },
    Thread : Threads
]

TypeOk ==
    /\  Locks \in SUBSET LockType

LocksAreCompatible == 
    \/  Cardinality(Locks) <= 1
    \/  \A lock \in Locks :
        lock.Type = "Read"

Invariant ==
    /\  TypeOk
    /\  LocksAreCompatible

Init ==
    /\  Locks \in SUBSET LockType
    /\  Invariant

Next ==
    /\  Locks' \in SUBSET LockType
    /\  Invariant'

Spec ==
    /\  Init
    /\  [][Next]_vars

Property ==
    /\  Spec
    /\  []Invariant

====