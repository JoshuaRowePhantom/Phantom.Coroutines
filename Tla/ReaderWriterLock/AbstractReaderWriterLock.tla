---- MODULE AbstractReaderWriterLock ----
EXTENDS FiniteSets, Integers

CONSTANT Threads

VARIABLE 
    Readers,
    Writers

vars == <<
    Readers,
    Writers
>>

TypeOk ==
    /\  Readers \in SUBSET Threads
    /\  Writers \in SUBSET Threads

Init ==
    /\  Readers = {}
    /\  Writers = {}

Next ==
    \/  /\  Readers' \in SUBSET Threads
        /\  Writers' = {}
    \/  /\  Readers' = {}
        /\  \E writer \in Threads :
            Writers' = { writer }

Spec ==
    /\  Init
    /\  [][Next]_vars

Invariant ==
    /\  Readers # {} => Writers = {}
    /\  Writers # {} => Readers = {}
    /\  Cardinality(Writers) <= 1

Property ==
    /\  Spec
    /\  []Invariant

====