---- MODULE ThreadPool_Correctness_5_Items_3_Threads ----
EXTENDS ThreadPool, TLC

CONSTANT t1, t2, t3
CONSTANT i1, i2, i3, i4, i5

MC_Threads == {t1, t2, t3}
MC_Items == {i1, i2, i3, i4, i5}

Symmetry == Permutations(MC_Threads) \union Permutations(MC_Items)
====