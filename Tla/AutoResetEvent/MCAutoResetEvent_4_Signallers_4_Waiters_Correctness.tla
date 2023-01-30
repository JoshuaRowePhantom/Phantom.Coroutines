---- MODULE MCAutoResetEvent_4_Signallers_4_Waiters_Correctness ----

EXTENDS AutoResetEvent, TLC

Symmetry == Permutations(SignallingThreads) \union Permutations(ListeningThreads)

====
