---- MODULE ThreadPool_Wakeup_Liveness_3_Items_3_Threads ----
EXTENDS ThreadPool_Wakeup, TLC

CONSTANT t1, t2, t3

MC_Items == 3
MC_Threads == {t1, t2, t3}
====