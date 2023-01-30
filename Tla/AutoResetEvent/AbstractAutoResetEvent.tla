---- MODULE AbstractAutoResetEvent ----

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

TypeOk ==
    /\  SetCount \in Nat
    /\  Listeners \in Seq(ListeningThreads)
    /\  ListenerStates \in [ ListeningThreads -> { "Idle", "Waiting", "Complete" }]

\* When the last listener has resumed, we infer that
\* the program terminates and destroys the AutoResetEvent.
Destroyed == \A listener \in ListeningThreads : ListenerStates[listener] = "Complete"

Init == 
    /\  SetCount = 0
    /\  Listeners = << >>
    /\  ListenerStates = [ thread \in ListeningThreads |-> "Idle" ]

Listen(thread) ==
    /\  ListenerStates[thread] = "Idle"
    /\  Assert(~Destroyed, "Shouldn't be destroyed if listening!")
    /\  
        \* A listening thread can add itself to the list of pending awaiters
        \/  
            /\  Listeners' = Listeners \o << thread >>
            /\  ListenerStates' = [ListenerStates EXCEPT ![thread] = "Waiting"]
            /\  UNCHANGED << SetCount >>
        \* If there are no pending awaiters, and the event is set,
        \* then the listener can be immediately released.
        \/  
            /\  SetCount > 1
            /\  Listeners = << >>
            /\  SetCount = 0
            /\  ListenerStates' = [ListenerStates EXCEPT ![thread] = "Completed"]

Set ==
    /\  ~Destroyed
    \* A set operation on an already-set event with no listeners is allowed
    /\  \/  /\  SetCount = 1
            /\  SetCount' = 1
            /\  ListeningThreads = << >>
    \* A Set operation can either increment the SetCount
    \* without releasing a listener,
        \/  /\  SetCount' = SetCount + 1
            /\  SetCount' < Len(Listeners) + 1
            /\  UNCHANGED << Listeners, ListenerStates >>
    \* Or the set operation can release the first listener, as though
    \* the listener has gone through Wake.
        \/  /\  SetCount = 0
            /\  Listeners # << >>
            /\  Listeners' = Tail(Listeners)
            /\  ListenerStates' = [ListenerStates EXCEPT ![Head(Listeners)] = "Complete"]
            /\  UNCHANGED << SetCount >>

Wake(thread) ==
    /\  Listeners # << >>
    /\  Assert(~Destroyed, "Shouldn't be destroyed if waking threads!")
    /\  Head(Listeners) = thread
    /\  SetCount > 0
    /\  SetCount' = SetCount - 1
    /\  Listeners' = Tail(Listeners)
    /\  ListenerStates' = [ListenerStates EXCEPT ![Head(Listeners)] = "Complete"]

Complete ==
    /\  Destroyed
    /\  UNCHANGED vars

Next ==
    \E thread \in ListeningThreads :
    \/  Listen(thread)
    \/  Set
    \/  Wake(thread)
    \/  Complete
    
Spec ==
    /\  Init
    /\  [][Next]_vars

Alias == [
    SetCount |-> SetCount,
    Listeners |-> Listeners,
    ListenerStates |-> ListenerStates,
    TypeOk |-> TypeOk,
    Destroyed |-> Destroyed,
    Set |-> Set
]

CanMakeProgress == []<>(Destroyed \/ ENABLED(Set))
SetCountIsAlwaysValid == SetCount <= Len(Listeners) + 1

Property ==
    /\  Spec
    /\  [](SetCountIsAlwaysValid)
    /\  CanMakeProgress

==== 