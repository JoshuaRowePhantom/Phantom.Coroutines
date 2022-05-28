---- MODULE ThreadPool_Liveness_3_Items_2_Threads ----
EXTENDS ThreadPool, TLC

CONSTANT t1, t2
CONSTANT i1, i2, i3

MC_Threads == {t1, t2}
MC_Items == {i1, i2, i3}
====