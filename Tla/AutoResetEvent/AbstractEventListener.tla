---- MODULE AbstractEventListener ----

VARIABLE State
vars == << State >>

TypeOk == State \in { "Idle", "Waiting", "Complete" }

Init == State = "Idle"

Wait == 
    /\ State = "Idle"
    /\ State' = "Waiting"

Complete ==
    /\ State' = "Complete"

Next ==
    \/  Wait
    \/  Complete

Spec ==
    /\  Init
    /\  [][Next]_vars

Property == 
    /\  Spec
    /\  [](TypeOk)

====
