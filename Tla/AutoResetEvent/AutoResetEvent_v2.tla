---- MODULE AutoResetEvent_v2 ----
EXTENDS Sequences, Integers

CONSTANT 
    ListeningThreads,
    SignallingThreads

VARIABLE 
    State,
    SetCount,
    Listeners,
    SignallerStates,
    ListenerStates

vars == <<
    State,
    SetCount,
    Listeners,
    SignallerStates,
    ListenerStates
>>

MapListenerState(state) ==
    IF state \in { "Idle", "Listen_AddToListeners" }
    THEN "Idle"
    ELSE IF state \in {"Waiting"}
    THEN "Waiting"
    ELSE "Complete"

AbstractEvent == 
    INSTANCE AbstractAutoResetEvent
    WITH 
    ListenerStates <- [ thread \in ListeningThreads |-> MapListenerState(ListenerStates[thread]) ]

AbstractEventSpec == AbstractEvent!Spec

TypeOk ==
    /\  AbstractEvent!TypeOk
    /\  State \in { "NotSignalled", "Signalling", "Signalled" }
    /\  SignallerStates \in [ SignallingThreads -> { 
            "Idle",
            "Set_Signalling",
            "Complete" 
        } ]
    /\  ListenerStates \in [ ListeningThreads -> { 
            "Idle",
            "Listen_AddToListeners",
            "Waiting",
            "Complete" 
        } ]
    /\  Listeners \in Seq(ListeningThreads)

Destroyed == AbstractEvent!Destroyed

Signaller_Goto(thread, state) ==
    SignallerStates' = [SignallerStates EXCEPT ![thread] = state]

Listener_Goto(thread, state) ==
    ListenerStates' = [ListenerStates EXCEPT ![thread] = state]

Init ==
    /\  State = "NotSignalled"
    /\  Listeners = << >>
    /\  SetCount = 0
    /\  SignallerStates = [
            signaller \in SignallingThreads |-> "Idle"
        ]
    /\  ListenerStates = [
            listener \in ListeningThreads |-> "Idle"
        ]

Listen(thread) == 
    /\  ListenerStates[thread] = "Idle"
    /\  \/  /\  State = "Signalled"
            /\  State' = "NotSignalled"
            /\  Listener_Goto(thread, "Complete")
            /\  UNCHANGED << SignallerStates, Listeners, SetCount >>
        \/  /\  State = "NotSignalled"
            /\  Listener_Goto(thread, "Listen_AddToListeners")
            /\  UNCHANGED << SignallerStates, State, Listeners, SetCount >>

Listen_AddToListeners(thread) ==
    /\  ListenerStates[thread] = "Listen_AddToListeners"
    /\  Listeners' = Listeners \o << thread >>
    /\  Listener_Goto(thread, "Waiting")
    /\  UNCHANGED << SignallerStates, State, SetCount >>

Set(thread) == 
    /\  SignallerStates[thread] = "Idle"
    /\  ~Destroyed
    /\  \/  /\  Listeners # << >>
            /\  Listeners' = Tail(Listeners)
            /\  Listener_Goto(Head(Listeners), "Complete")
    /\  UNCHANGED << State, SetCount, SignallerStates >>

Set_Signalling(thread) == FALSE
    /\
    /\  SignallerStates[thread] = "Set_Signalling"
    /\  \/  /\  State = "NotSignalled"
            /\  State' = "Signalling"
            /\  Signaller_Goto(thread, "Idle")
        \/  /\  State = "Signalling"
            /\  Signaller_Goto(thread, "Idle")
            /\  UNCHANGED << State >>
    /\ UNCHANGED << Listeners, ListenerStates >>

Complete ==
    /\  Destroyed
    /\  \A thread \in SignallingThreads : SignallerStates[thread] \in { "Idle", "Complete" }
    /\  UNCHANGED vars

Next ==
    \/  \E thread \in ListeningThreads :
        \/  Listen(thread)
        \/  Listen_AddToListeners(thread)
    \/  \E thread \in SignallingThreads :
        \/  Set(thread)
        \/  Set_Signalling(thread)
    \/  Complete

Spec ==
    /\  Init
    /\  [][Next]_vars
    /\  \A thread \in ListeningThreads :
        /\  WF_vars(Listen_AddToListeners(thread))

Alias ==
    [
        ListenerStates |-> ListenerStates,
        Listeners |-> Listeners,
        SignallerStates |-> SignallerStates,
        States |-> State,
        Destroyed |-> Destroyed,
        AbstractEvent |-> AbstractEvent!Alias,
        SetCount |-> SetCount,
        ListeningThreads |-> [ thread \in ListeningThreads |-> 
            [
                Listen_Enabled |-> ENABLED(Listen(thread)),
                Listen_AddToListeners_Enabled |-> ENABLED(Listen_AddToListeners(thread))
            ]
        ],
        SignallingThreads |-> [ thread \in SignallingThreads |->
            [
                Set_Enabled |-> ENABLED(Set(thread)),
                Set_Signalling_Enabled |-> ENABLED(Set_Signalling(thread))
            ]
        ]
    ]

Property == 
    /\  AbstractEvent!Property
    /\  Spec

====
