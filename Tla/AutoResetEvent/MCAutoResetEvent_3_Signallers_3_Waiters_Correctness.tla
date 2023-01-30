---- MODULE MCAutoResetEvent_3_Signallers_3_Waiters_Correctness ----

EXTENDS AutoResetEvent, TLC

Symmetry == Permutations(SignallingThreads) \union Permutations(ListeningThreads)

====
