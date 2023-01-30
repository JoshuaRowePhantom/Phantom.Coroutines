---- MODULE MCAutoResetEvent_4_Signallers_4_Waiters_Correctness ----

EXTENDS AutoResetEvent, TLC
CONSTANT l1, l2, l3, l4, s1, s2, s3, s4
MCListeningThreads == { l1, l2 }
MCSignallingThreads == { s1, s2 }
Symmetry == Permutations(MCSignallingThreads) \union Permutations(MCListeningThreads)

Checks == Len(PendingAwaiters) < 2
====
