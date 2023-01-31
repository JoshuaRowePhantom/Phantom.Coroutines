---- MODULE AbstractAutoResetEvent ----
(*

An auto reset event that supports multiple awaiters.
Awaiters must be woken approximately in order that they
are enqueued. The approximation is that:

Any series of _n_ Listen operations that occur
without any intervening Set operations must ensure
that all such listeners are woken by _n_ Set operations
before any later Listen operations are woken.

 *)
EXTENDS Sequences, Naturals, TLC

CONSTANT 
    ListeningThreads

VARIABLE 
    SetCount,
    Listeners,
    ListenerStates

vars == <<
    SetCount,
    Listeners,
    ListenerStates
>>

LOCAL AbstractListener(L) == INSTANCE AbstractEventListener WITH State <- ListenerStates[L]

ListenerStatesType == [ ListeningThreads -> { "Idle", "Waiting", "Complete" }]

TypeOk ==
    /\  SetCount \in Nat
    /\  Listeners \in Seq(ListeningThreads)
    /\  ListenerStates \in ListenerStatesType

Init == 
    /\  SetCount = 0
    /\  Listeners = << >>
    /\  ListenerStates = [ thread \in ListeningThreads |-> "Idle" ]

Listen(thread) ==
    /\  ListenerStates[thread] = "Idle"
    /\  
        \* A listening thread can add itself to the list of pending awaiters
        \/  
            /\  Listeners' = Listeners \o << thread >>
            /\  ListenerStates' = [ListenerStates EXCEPT ![thread] = "Waiting"]
            /\  UNCHANGED << SetCount >>
        \* If there are more setcounts than there are awaiters,
        \* the listener can be immediately released.
        \/  
            /\  SetCount > Len(Listeners)
            /\  SetCount' = SetCount - 1
            /\  ListenerStates' = [ListenerStates EXCEPT ![thread] = "Complete"]
            /\  UNCHANGED << Listeners >>

Set ==
    \* A set operation on an already-set event with no listeners is allowed
    /\  \/  /\  SetCount = 1
            /\  SetCount' = 1
            /\  Listeners = << >>
            /\  UNCHANGED << Listeners, ListenerStates >>
    \* A Set operation can either increment the SetCount
    \* without releasing a listener,
        \/  /\  SetCount' = SetCount + 1
            /\  SetCount' <= Len(Listeners) + 1
            /\  UNCHANGED << Listeners, ListenerStates >>
    \* Or the set operation can release the first listener, as though
    \* the listener has gone through Wake.
        \/  /\  SetCount = 0
            /\  Listeners # << >>
            /\  Listeners' = Tail(Listeners)
            /\  ListenerStates' = [ListenerStates EXCEPT ![Head(Listeners)] = "Complete"]
            /\  UNCHANGED << SetCount >>

\* Any number of threads can wake simultaneously,
\* up to the SetCount.
Wake ==
    \E count \in 1..Len(Listeners) :
    /\  SetCount >= count
    /\  SetCount' = SetCount - count
    /\  Listeners' = SubSeq(Listeners, count + 1, Len(Listeners))
    /\  ListenerStates' = [
            listener \in ListeningThreads |->
                IF \E item \in 1..count : Listeners[item] = listener
                THEN "Complete"
                ELSE ListenerStates[listener]
        ]

Next ==
    \E thread \in ListeningThreads :
    \/  Listen(thread)
    \/  Set
    \/  Wake

Spec ==
    /\  Init
    /\  [][Next]_vars
    /\  \A thread \in ListeningThreads :
        WF_vars(Wake)

Alias == [
    SetCount |-> SetCount,
    Listeners |-> Listeners,
    ListenerStates |-> ListenerStates,
    TypeOk |-> TypeOk,
    Set |-> Set,
    Listen |-> [ thread \in ListeningThreads |-> Listen(thread) ],
    Wake |-> Wake,
    Check |->  SetCount > Len(Listeners)
    (*
            \E thread \in ListeningThreads :
            /\  SetCount > Len(Listeners)
            /\  SetCount' = SetCount - 1
            /\  ListenerStates' = [ListenerStates EXCEPT ![thread] = "Complete"] *)

]

CanMakeProgress == []<>(ENABLED(Set))
SetCountIsAlwaysValid == SetCount <= Len(Listeners) + 1

Property ==
    /\  Spec
    /\  [](SetCountIsAlwaysValid)
    /\  CanMakeProgress
    /\  TypeOk
    \* Have to comment this out until this is resolved:
    \* https://github.com/tlaplus/tlaplus/issues/687
    \*  /\  \A thread \in ListeningThreads :
    \*    /\  AbstractListener(thread)!Property
    /\  [][
            \A thread \in ListeningThreads :
                /\
                    \/  AbstractListener(thread)!Next
                    \/  UNCHANGED AbstractListener(thread)!vars
                /\  AbstractListener(thread)!TypeOk
        ]_vars

====
