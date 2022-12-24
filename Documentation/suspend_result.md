
== suspend_result.h ==

There are situations where it is useful to know whether a given asynchronous operation
suspended.  For example: when waiting on a lock, it can be useful to know whether the
lock wait actually resulted in a suspension so that the resuming coroutine can
decide to reschedule on a threadpool thread rather than blocking the coroutine that
released the lock.

```suspend_result``` is a class that can be interjected into a co_await expression
to learn whether the coroutine was suspended.  It has one member:

```
// Determine whether suspend_result believes the calling coroutine was suspended.
bool did_suspend() const;
```

It is used like this:

```
suspend_result suspendResult;
auto returnValue = co_await (suspendResult << SomeAsyncRoutine());
if (suspendResult.did_suspend()) {
    // ... handle that here.
}
```

It is designed this way to enable detecting suspension in the case of an exception,
as well as ensuring that awaiting any object type does not affect the result,
especially by not introducing extra copy or move operations.

An example with exception handling:

```
suspend_result suspendResult;
try
{
    auto returnValue = co_await (suspendResult << SomeAsyncRoutine());
    if (suspendResult.did_suspend()) {
        // ... handle that here.
    }
    // ... success logic here ...
}
catch (...)
{
    if (suspendResult.did_suspend()) {
        // ... handle that here.
    }
    // ... exception logic here ...
}
```

A single suspend_result object can be reused by multiple consecutive injections;
in this case, if any of the injections suspended, then the suspend_result will
indicate that the coroutine suspended.  This is useful if there are multiple
co_await expressions that might suspend and have potentially many resumers
on each co_await expression, but the contention in all but the last resumption is cheap,
so that it is preferable to resume all but the last co_await expressions on the caller's
thread, unless none of the co_await expressions actually suspended, in which case
event the last co_await expression should execute on the caller's thread.  For example:

```
task<ProcessedItem> ProcessItem()
{
    suspend_result suspendResult;
    
    // This event is "set" most of the time,
    // but when it isn't set, many ProcessItem resumptions will
    // be piled up on it.
    co_await (suspendResult << m_startProcessingEvent);

    // When m_startProcesingEvent is first set, a lot of coroutines
    // will try to acquire this lock, but because we resume from awaiting
    // m_startProcessingEvent in the event::set()'s thread, they won't
    // attempt to do this until we resume on another thread.
    auto scopedLock = co_await (suspendResult << m_mutex.scoped_lock());
    auto itemToProcess = std::move(m_queue.front());

    // This might release another ProcessItem() call,
    // which if it ran DoExpensiveProcessing immediately would
    // block this coroutine from doing useful work.
    // The suspendResult collected from the scoped_lock
    // allows that other ProcessItem() call to detect that it
    // should reschedule on the threadpool.
    scopedLock.release();

    // When both m_startProcessingEvent AND scopedLock are acquired without suspending,
    // we assume that the calling thread is actually interested in the value
    // of ProcessedItem and so we don't bother rescheduling onto another thread.
    if (suspendResult.did_suspend())
    {
        co_await m_threadPool.schedule();
    }

    co_return DoExpensiveProcessing(itemToProcess);
}
```

```suspend_result``` determines that a coroutine suspended if co_await is executed on an 
```is_awaiter``` object where either:

  * ```await_suspend``` returns ```void```
  * ```await_suspend``` returns the boolean value ```true```
  * ```await_suspend``` returns a ```std::coroutine_handle<>``` different from the handle passed in

It's possible there are false positives.  In particular, ```task<>``` /always/ returns a
different ```std::coroutine_handle<>``` and will always be marked as suspended, and 
```shared_task<>``` will always return a different ```std::coroutine_handle<>``` whenever
the task is not yet completed.  It isn't possible to accurately detect that a ```task<>```
or ```shared_task<>``` executed without suspending.
