---- MODULE AutoResetEvent_v2 ----
EXTENDS Sequences, Integers, TLC

CONSTANT 
    ListeningThreads,
    SignallingThreads

VARIABLE 
    SetCount,
    WaiterCount,
    EnqueuedListeners,
    UnservicedListeners,
    ListenersToService,
    FetchedListeners,
    ListenerStates,
    FetchingCount,
    pc

RECURSIVE Sum(_)

RECURSIVE AccumulateImpl(_, _, _, _)

AccumulateImpl(F(_, _), I, D, Domain) ==
    IF Domain = {} THEN I ELSE 
    LET x == CHOOSE y \in Domain : TRUE IN
    F(D[x], AccumulateImpl(F, I, D, Domain \ { x }))

Accumulate(F(_, _), I, D) ==
    AccumulateImpl(F, I, D, DOMAIN D)

Add(a,b) == a + b
Sum(F) == Accumulate(Add, 0, F)

RECURSIVE ThreadIsIn(_, _)
ThreadIsIn(thread, sequence) ==
    IF sequence = << >> THEN FALSE
    ELSE IF Head(sequence) = thread THEN TRUE
    ELSE ThreadIsIn(thread, Tail(sequence))

AbstractSetCount == SetCount

AllThreads == ListeningThreads \union SignallingThreads

\* There will only ever be a single FetchedListeners value that is non-empty.
\* Retrieve it with NonZeroFetchedListeners, or if there are non non-empty return empty.
AllFetchedListeners == { FetchedListeners[t] : t \in AllThreads }
NonZeroFetchedListeners ==
    IF \E a \in AllFetchedListeners : a # << >> THEN CHOOSE a \in AllFetchedListeners : a # << >> ELSE << >>

AbstractListeners ==
    SubSeq(
        UnservicedListeners \o NonZeroFetchedListeners \o EnqueuedListeners,
        1,
        WaiterCount)

AbstractListenerStates == [ 
    thread \in ListeningThreads |->
        IF  \/  ListenerStates[thread] = "Complete"
            \/  \E signaller \in AllThreads : ThreadIsIn(thread, ListenersToService[signaller])
        THEN "Complete"
        ELSE IF ThreadIsIn(thread, AbstractListeners)
        THEN "Waiting"
        ELSE "Idle"
]

AbstractEvent == 
    INSTANCE AbstractAutoResetEvent
    WITH 
    Listeners <- AbstractListeners,
    SetCount <- AbstractSetCount,
    ListenerStates <- AbstractListenerStates

AbstractEventSpec == AbstractEvent!Spec

TypeOk ==
    /\  AbstractEvent!TypeOk
    /\  ListenerStates \in [ ListeningThreads -> { 
            "Idle",
            "Listen_AddToListeners",
            "Waiting",
            "Complete" 
        } ]
    /\  EnqueuedListeners \in Seq(ListeningThreads)
    /\  UnservicedListeners \in Seq(ListeningThreads)
    /\  SetCount \in Nat
    /\  WaiterCount \in Nat
    /\  FetchingCount \in [ AllThreads -> Nat ]
    /\  ListenersToService \in [ AllThreads -> Seq(ListeningThreads) ]

Destroyed == 
    /\  \A thread \in ListeningThreads : ListenerStates[thread] = "Complete"
    /\  \A thread \in SignallingThreads : pc[thread] \in { "Done", "Set", "Resume_SignalListeners" }

Min(S) ==
    CHOOSE s1 \in S : \A s2 \in S : s2 >= s1

(* --algorithm AutoResetEvent_v2 

variables
    SetCount = 0,
    WaiterCount = 0,
    EnqueuedListeners = << >>,
    UnservicedListeners = << >>,
    ListenerStates = [
        listener \in ListeningThreads |-> "Idle"
    ];

procedure ResumeAwaiters(
    FetchingCount = 0
)
variable
    ListenersToService = << >>,
    FetchedListeners = << >>
begin

Resume_FetchListenersToService:
    while FetchingCount # 0 do
        assert ~Destroyed;

        \* This requires a single atomic exchange of EnqueuedListeners
        FetchedListeners := EnqueuedListeners;
        EnqueuedListeners := << >>;

Resume_DecrementCounts_and_AdjustLists:
        assert ~Destroyed;
        ListenersToService := ListenersToService \o
            SubSeq(
                UnservicedListeners \o FetchedListeners, 
                1, 
                FetchingCount)
        ||
        UnservicedListeners := SubSeq(
            UnservicedListeners \o FetchedListeners, 
            FetchingCount + 1, 
            Len(UnservicedListeners \o FetchedListeners));

        FetchedListeners := << >>;

        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        SetCount := SetCount - FetchingCount;
        WaiterCount := WaiterCount - FetchingCount;
        if SetCount > 0 /\ WaiterCount > 0 then
            FetchingCount := Min({ SetCount, WaiterCount });
        else
            FetchingCount := 0;
        end if;
    end while;
    
Resume_SignalListeners:
    while ListenersToService # << >> do
        ListenerStates[Head(ListenersToService)] := "Complete";
        ListenersToService := Tail(ListenersToService);
    end while;
    return;
end procedure;

fair process ListeningThread \in ListeningThreads
begin
    
Listen:-
    either
        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        await SetCount > WaiterCount;
        SetCount := SetCount - 1;
        ListenerStates[self] := "Complete";
    or
        \* This requires an atomic read of SetCount + WaiterCount
        \* simultaneously.
        await SetCount <= WaiterCount;

Listen_EnqueueWaiter:
        EnqueuedListeners := EnqueuedListeners \o << self >>;
        ListenerStates[self] := "Waiting";

Listen_IncrementWaiterCount:
        \* This requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        WaiterCount := WaiterCount + 1;
        if SetCount > 0 /\ WaiterCount = 1 then
            call ResumeAwaiters(
                Min({ SetCount, WaiterCount }));
        end if;

Listen_Wait:
        await ListenerStates[self] = "Complete";
    end either;

end process;

fair process SignallingThread \in SignallingThreads
begin
Set:-
    while ~Destroyed do
        \* Set is a noop when SetCount >= WaiterCount + 1
        \* This action requires an atomic read modify write of SetCount + WaiterCount
        \* simultaneously.
        await SetCount < WaiterCount + 1;
        SetCount := Min({SetCount + 1, WaiterCount + 1});
        if SetCount = 1 /\ WaiterCount > 0 then
            call ResumeAwaiters(
                Min({ SetCount, WaiterCount }));
            goto Set;
        end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2a5865a9" /\ chksum(tla) = "78205c21")
VARIABLES SetCount, WaiterCount, EnqueuedListeners, UnservicedListeners, 
          ListenerStates, pc, stack, FetchingCount, ListenersToService, 
          FetchedListeners

vars == << SetCount, WaiterCount, EnqueuedListeners, UnservicedListeners, 
           ListenerStates, pc, stack, FetchingCount, ListenersToService, 
           FetchedListeners >>

ProcSet == (ListeningThreads) \cup (SignallingThreads)

Init == (* Global variables *)
        /\ SetCount = 0
        /\ WaiterCount = 0
        /\ EnqueuedListeners = << >>
        /\ UnservicedListeners = << >>
        /\ ListenerStates =                  [
                                listener \in ListeningThreads |-> "Idle"
                            ]
        (* Procedure ResumeAwaiters *)
        /\ FetchingCount = [ self \in ProcSet |-> 0]
        /\ ListenersToService = [ self \in ProcSet |-> << >>]
        /\ FetchedListeners = [ self \in ProcSet |-> << >>]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in ListeningThreads -> "Listen"
                                        [] self \in SignallingThreads -> "Set"]

Resume_FetchListenersToService(self) == /\ pc[self] = "Resume_FetchListenersToService"
                                        /\ IF FetchingCount[self] # 0
                                              THEN /\ Assert(~Destroyed, 
                                                             "Failure of assertion at line 119, column 9.")
                                                   /\ FetchedListeners' = [FetchedListeners EXCEPT ![self] = EnqueuedListeners]
                                                   /\ EnqueuedListeners' = << >>
                                                   /\ pc' = [pc EXCEPT ![self] = "Resume_DecrementCounts_and_AdjustLists"]
                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Resume_SignalListeners"]
                                                   /\ UNCHANGED << EnqueuedListeners, 
                                                                   FetchedListeners >>
                                        /\ UNCHANGED << SetCount, WaiterCount, 
                                                        UnservicedListeners, 
                                                        ListenerStates, stack, 
                                                        FetchingCount, 
                                                        ListenersToService >>

Resume_DecrementCounts_and_AdjustLists(self) == /\ pc[self] = "Resume_DecrementCounts_and_AdjustLists"
                                                /\ Assert(~Destroyed, 
                                                          "Failure of assertion at line 126, column 9.")
                                                /\ /\ ListenersToService' = [ListenersToService EXCEPT ![self] =                   ListenersToService[self] \o
                                                                                                                 SubSeq(
                                                                                                                     UnservicedListeners \o FetchedListeners[self],
                                                                                                                     1,
                                                                                                                     FetchingCount[self])]
                                                   /\ UnservicedListeners' =                    SubSeq(
                                                                             UnservicedListeners \o FetchedListeners[self],
                                                                             FetchingCount[self] + 1,
                                                                             Len(UnservicedListeners \o FetchedListeners[self]))
                                                /\ FetchedListeners' = [FetchedListeners EXCEPT ![self] = << >>]
                                                /\ SetCount' = SetCount - FetchingCount[self]
                                                /\ WaiterCount' = WaiterCount - FetchingCount[self]
                                                /\ IF SetCount' > 0 /\ WaiterCount' > 0
                                                      THEN /\ FetchingCount' = [FetchingCount EXCEPT ![self] = Min({ SetCount', WaiterCount' })]
                                                      ELSE /\ FetchingCount' = [FetchingCount EXCEPT ![self] = 0]
                                                /\ pc' = [pc EXCEPT ![self] = "Resume_FetchListenersToService"]
                                                /\ UNCHANGED << EnqueuedListeners, 
                                                                ListenerStates, 
                                                                stack >>

Resume_SignalListeners(self) == /\ pc[self] = "Resume_SignalListeners"
                                /\ IF ListenersToService[self] # << >>
                                      THEN /\ ListenerStates' = [ListenerStates EXCEPT ![Head(ListenersToService[self])] = "Complete"]
                                           /\ ListenersToService' = [ListenersToService EXCEPT ![self] = Tail(ListenersToService[self])]
                                           /\ pc' = [pc EXCEPT ![self] = "Resume_SignalListeners"]
                                           /\ UNCHANGED << stack, 
                                                           FetchingCount, 
                                                           FetchedListeners >>
                                      ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                           /\ ListenersToService' = [ListenersToService EXCEPT ![self] = Head(stack[self]).ListenersToService]
                                           /\ FetchedListeners' = [FetchedListeners EXCEPT ![self] = Head(stack[self]).FetchedListeners]
                                           /\ FetchingCount' = [FetchingCount EXCEPT ![self] = Head(stack[self]).FetchingCount]
                                           /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                           /\ UNCHANGED ListenerStates
                                /\ UNCHANGED << SetCount, WaiterCount, 
                                                EnqueuedListeners, 
                                                UnservicedListeners >>

ResumeAwaiters(self) == Resume_FetchListenersToService(self)
                           \/ Resume_DecrementCounts_and_AdjustLists(self)
                           \/ Resume_SignalListeners(self)

Listen(self) == /\ pc[self] = "Listen"
                /\ \/ /\ SetCount > WaiterCount
                      /\ SetCount' = SetCount - 1
                      /\ ListenerStates' = [ListenerStates EXCEPT ![self] = "Complete"]
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                   \/ /\ SetCount <= WaiterCount
                      /\ pc' = [pc EXCEPT ![self] = "Listen_EnqueueWaiter"]
                      /\ UNCHANGED <<SetCount, ListenerStates>>
                /\ UNCHANGED << WaiterCount, EnqueuedListeners, 
                                UnservicedListeners, stack, FetchingCount, 
                                ListenersToService, FetchedListeners >>

Listen_EnqueueWaiter(self) == /\ pc[self] = "Listen_EnqueueWaiter"
                              /\ EnqueuedListeners' = EnqueuedListeners \o << self >>
                              /\ ListenerStates' = [ListenerStates EXCEPT ![self] = "Waiting"]
                              /\ pc' = [pc EXCEPT ![self] = "Listen_IncrementWaiterCount"]
                              /\ UNCHANGED << SetCount, WaiterCount, 
                                              UnservicedListeners, stack, 
                                              FetchingCount, 
                                              ListenersToService, 
                                              FetchedListeners >>

Listen_IncrementWaiterCount(self) == /\ pc[self] = "Listen_IncrementWaiterCount"
                                     /\ WaiterCount' = WaiterCount + 1
                                     /\ IF SetCount > 0 /\ WaiterCount' = 1
                                           THEN /\ /\ FetchingCount' = [FetchingCount EXCEPT ![self] = Min({ SetCount, WaiterCount' })]
                                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeAwaiters",
                                                                                            pc        |->  "Listen_Wait",
                                                                                            ListenersToService |->  ListenersToService[self],
                                                                                            FetchedListeners |->  FetchedListeners[self],
                                                                                            FetchingCount |->  FetchingCount[self] ] >>
                                                                                        \o stack[self]]
                                                /\ ListenersToService' = [ListenersToService EXCEPT ![self] = << >>]
                                                /\ FetchedListeners' = [FetchedListeners EXCEPT ![self] = << >>]
                                                /\ pc' = [pc EXCEPT ![self] = "Resume_FetchListenersToService"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "Listen_Wait"]
                                                /\ UNCHANGED << stack, 
                                                                FetchingCount, 
                                                                ListenersToService, 
                                                                FetchedListeners >>
                                     /\ UNCHANGED << SetCount, 
                                                     EnqueuedListeners, 
                                                     UnservicedListeners, 
                                                     ListenerStates >>

Listen_Wait(self) == /\ pc[self] = "Listen_Wait"
                     /\ ListenerStates[self] = "Complete"
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << SetCount, WaiterCount, EnqueuedListeners, 
                                     UnservicedListeners, ListenerStates, 
                                     stack, FetchingCount, ListenersToService, 
                                     FetchedListeners >>

ListeningThread(self) == Listen(self) \/ Listen_EnqueueWaiter(self)
                            \/ Listen_IncrementWaiterCount(self)
                            \/ Listen_Wait(self)

Set(self) == /\ pc[self] = "Set"
             /\ IF ~Destroyed
                   THEN /\ SetCount < WaiterCount + 1
                        /\ SetCount' = Min({SetCount + 1, WaiterCount + 1})
                        /\ IF SetCount' = 1 /\ WaiterCount > 0
                              THEN /\ /\ FetchingCount' = [FetchingCount EXCEPT ![self] = Min({ SetCount', WaiterCount })]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ResumeAwaiters",
                                                                               pc        |->  "Set",
                                                                               ListenersToService |->  ListenersToService[self],
                                                                               FetchedListeners |->  FetchedListeners[self],
                                                                               FetchingCount |->  FetchingCount[self] ] >>
                                                                           \o stack[self]]
                                   /\ ListenersToService' = [ListenersToService EXCEPT ![self] = << >>]
                                   /\ FetchedListeners' = [FetchedListeners EXCEPT ![self] = << >>]
                                   /\ pc' = [pc EXCEPT ![self] = "Resume_FetchListenersToService"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Set"]
                                   /\ UNCHANGED << stack, FetchingCount, 
                                                   ListenersToService, 
                                                   FetchedListeners >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << SetCount, stack, FetchingCount, 
                                        ListenersToService, FetchedListeners >>
             /\ UNCHANGED << WaiterCount, EnqueuedListeners, 
                             UnservicedListeners, ListenerStates >>

SignallingThread(self) == Set(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: ResumeAwaiters(self))
           \/ (\E self \in ListeningThreads: ListeningThread(self))
           \/ (\E self \in SignallingThreads: SignallingThread(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ListeningThreads : /\ WF_vars((pc[self] # "Listen") /\ ListeningThread(self))
                                          /\ WF_vars(ResumeAwaiters(self))
        /\ \A self \in SignallingThreads : /\ WF_vars((pc[self] # "Set") /\ SignallingThread(self))
                                           /\ WF_vars(ResumeAwaiters(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Alias ==
    [
        pc |-> pc,
        ListenerStates |-> ListenerStates,
        EnqueuedListeners |-> EnqueuedListeners, 
        UnservicedListeners |-> UnservicedListeners,
        Destroyed |-> Destroyed,
        AbstractEvent |-> AbstractEvent!Alias,
        SetCount |-> SetCount,
        WaiterCount |-> WaiterCount,
        ListeningThreads |-> [ thread \in ListeningThreads |-> 
            [
                Listen_Enabled |-> ENABLED(Listen(thread))
            ]
        ],
        SignallingThreads |-> [ thread \in SignallingThreads |->
            [
                Set_Enabled |-> ENABLED(Set(thread))
            ]
        ],
        FetchingCount |-> FetchingCount,
        FetchedListeners |-> FetchedListeners,
        ListenersToService |-> ListenersToService
    ]

Property == 
    /\  AbstractEvent!Property
    /\  Spec

====
