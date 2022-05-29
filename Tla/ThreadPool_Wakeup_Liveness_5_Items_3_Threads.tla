---- MODULE ThreadPool_Wakeup_Liveness_5_Items_3_Threads ----
EXTENDS ThreadPool_Wakeup, TLC

CONSTANT t1, t2, t3

MC_Items == 5
MC_Threads == {t1, t2, t3}
====