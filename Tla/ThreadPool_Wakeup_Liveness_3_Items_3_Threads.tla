---- MODULE ThreadPool_Wakeup_Liveness_3_Items_3_Threads ----
EXTENDS ThreadPool_Wakeup, TLC

CONSTANT w1, w2, r3

MC_Items == 3
MC_WorkerThreads == {w1, w2}
MC_RemoteThreads == {r3}
====