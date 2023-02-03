---- MODULE AbstractFifoQueue ----
EXTENDS Sequences, Integers

CONSTANT 
    Items

VARIABLE
    Queue

Init == Queue = << >>

Enqueue(item) ==
    /\  Queue' = Queue \o << item >>

Dequeue(item) ==
    /\  Queue # << >>
    /\  Queue[1] = item
    /\  Queue' = Tail(Queue)

Next ==
    \E item \in Items :
    \/  Enqueue(item)
    \/  Dequeue(item)

Spec ==
    /\  Init
    /\  [][Next]_Queue

Constraint == Len(Queue) < 10

====
