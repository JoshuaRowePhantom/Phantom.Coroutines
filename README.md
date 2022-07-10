= Phantom.Coroutines =

A C++20 coroutine library.

== Goals ==

This is effort, much inspired by Lewis Baker's cppcoro library, is an ab-initio
set of C++ classes designed to implement coroutines with great efficiency and
flexibility.  This implementation is intended to work _only_ on compilers
with the latest and greatest features, especially symmetric transfer.

The coroutines defined by C++20 are -awesome-, but there are some non-straightforward
results from it that this library attempts to solve.  Most especially, deriving
new task / promise types from an existing library is extremely difficult.  The
coroutine_handle<T>::from_promise method requires the precise type of the
promise object; using a derived class is disallowed.  This library attempts
to solve that problem by documenting inheritance points and requirements.

There are other non-trivial consequences of using coroutines
naively that result in low-performance applications.  For example, ordinary implementations
of mutexes result in degradation of parallelization; this library provides primitive operations
to support maintaining parallelism.

This is a header-only library by design.  

This library does not provide platform-specific IO primitives.  It provides only those
primitives that are implementable only using the C++ standard and common extensions.

This library include Visual Studio Natvis visualizers for many of the embedded types.

By and large, this library aims to be source-level compatible with cppcoro.  Cppcoro namespaces,
includes, and type aliases are provided.

== Using ==

Put the ```include/Phantom.Coroutines``` directory in your include path.  Then, 
```#include``` the header that you desire:

```
import <Phantom.Coroutines/task.h>;
```

The contents of the ```Phantom::Coroutines``` namespace are open for use.  Everything
in ```Phantom::Coroutines::detail``` is undocumented.  At some point, this will be
enforced through C++ modules.

The rest of this document describes specific header file functionality.

== task.h ==

Task.h provides an extensible task<> implementation for implementing coroutines
that have a single awaiter.  The coroutine is started when the task is co_await'ed.
This implementation is particularly cheap, and doesn't even use atomic operations.
The only support operation on a task is to move it and to co_await it once.
Upon co_await'ing the task, the coroutine is started.  When the coroutine completes,
the awaiting coroutine is resumed via symmetric transfer, and the return value
or exception is propagated to the caller.

The result type of the task is a reference to the type parameter to task unless the task
returns void.  This is done to permit using the result of a task with no additional
copying.

The default return type of the task is void, so a typical usage is:

```
task<> DoSomethingThatDoesntReturnAnything() { co_return; }
```

For extensibility, this file provides the basic_task and basic_task_promise classes, which
accept a TaskTraits type parameter that glues together the task and promise types.

This file provides the following classes and concepts:

```
template<
    typename Traits
> concept TaskTraits;

template<
    typename Traits
> concept VoidTaskTraits;

template<
    typename Traits
> concept ReferenceTaskTraits;

template<
    TaskTraits Traits
> class basic_task;

template<
    TaskTraits Traits
> class basic_task_promise;
```

=== TaskTraits ===

The TaskTraits, VoidTaskTraits, and ReferenceTaskTraits concepts are defined as:

```
// basic_task_promise and basic_task require a type argument matching TaskTraits.
template<
    typename Traits
> concept TaskTraits = requires
{
    // The basic_task_promise-derived class that implements the promise type.
    typename Traits::promise_type;

    // The basic_task-derived class that implements the future type.
    typename Traits::future_type;

    // The result type of the task.
    typename Traits::result_type;
};

// Helper for matching task traits for result_type of void.
template<
    typename Traits
> concept VoidTaskTraits =
TaskTraits<Traits>
&&
std::same_as<void, typename Traits::result_type>;

// Helper for matching task traits for result_type of T& or T&&.
template<
    typename Traits
> concept ReferenceTaskTraits =
TaskTraits<Traits>
&&
std::is_reference_v<typename Traits::result_type>;
```

=== Deriving ===

An implementor can derive a new set of task and task_promise classes
by declaring a TypeTraits class and writing new classes that derive from
basic_task or basic_task_promise:

```
template<
    Result
> class my_task;

template<
    Result
> class my_task_promise;

template<
    Result
>
struct my_task_traits
{
    typedef my_task<Result> future_type;
    typedef my_task_promise<Result> promise_type;
    typedef Result result_type;
};

template<
    Result
> class my_task
    :
public basic_task<
    my_task_traits<Result>
>
{
    // ... your logic here
};

template<
    Result
> class my_task_promise
:
public basic_task_promise<
    my_task_traits<Result>
>
{
    // ... your logic here
};
```

The basic_task_promise implementation of get_return_object returns an aggregate-initialize future_type
passing in *this to the future_type.  This behavior can be changed by declaring a new get_return_object;
one might do this to write a promise_type that captures the argument list, for example.

== sync_wait.h ==

There are times when it is necessary to wait for the result of coroutine synchronously.  This is
especially true for the ```main()``` function of a program.  ```sync_wait.h``` provides two primitives
for this:

```
template<
    is_awaitable TAwaitable
> decltype(auto) as_future(
    TAwaitable&& awaitable
) -> std::future<awaitable_result_type_t<TAwaitable>>;

template<
    is_awaitable TAwaitable
> decltype(auto) sync_wait(
    TAwaitable&& awaitable
) -> awaitable_result_type_t<TAwaitable>;
```

Note that the restrictions on std::future apply to sync_wait: a future cannot return an rvalue-reference.

```as_future()``` performs a co_await on the awaitable object before returning the ```std::future``` object.  Thus,
it can be used to proactively start a coroutine.  Discarding the future object will result in the coroutine
running to completion.

== type_traits.h ==

This file contains concepts and structures to help with template metaprogramming.

```
// Tests to see if a type is an awaiter, meaning it has the await_ready,
// await_suspend, and await_resume methods.
template<
    typename TAwaiter
>
concept is_awaiter;

// Tests to see if a type has an awaiter-returning operator co_await.
template<
    typename TAwaitable
> concept has_co_await;

// Tests to see if a type can be co_await'ed, either because it has an operator co_await,
// or is an awaiter itself.
template<
    typename TAwaitable
> concept is_awaitable;

// Get the result type of a co_await'able object, as the ```type``` member.
template<
    is_awaitable TAwaitable
>
struct awaitable_result_type;

// Get the results type of co_await'able object.
template<
    is_awaitable TAwaitable
>
using awaitable_result_type_t = awaitable_result_type<TAwaitable>::type;
```

=== Implementation Notes ===

```task<Result>``` stores its return value in the task object itself and releases
the promise object as soon as the task's awaiter is resumed.  Thus, promises
that embody a large amount of state will be released quickly, and the task's
state does not bloat the promise state.

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

== single_consumer_promise.h ==

This class provides push-based completion scheme.  A single coroutine at a time 
can co_await the single_consumer_promise.  Some other thread can call ```emplace(...)```
to construct a value to return to the waiting coroutine.  Only one call
to ```emplace(...)``` can be made.  

