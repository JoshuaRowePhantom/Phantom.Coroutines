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

== Using ==

Put the ```include/Phantom.Coroutines``` directory in your include path.  Then, 
```#include``` the header that you desire:

```
#include <Phantom.Coroutines/task.h>
```

The contents of the ```Phantom::Coroutines``` namespace are open for use.  Everything
in ```Phantom::Coroutines::detail``` is undocumented.  At some point, this will be
enforced through C++ modules.

The rest of this document describes specific header file functionality.

== task.h ==

Task.h provides an extensible task<> implementation for implementing coroutines
that have a single awaiter.  The coroutine is started when the task is co_await'ed.
This implementation is particularly cheap, and doesn't even use atomic operations.
The only support operation on a task is to co_await it; it cannot be moved or copied.
Upon co_await'ing the task, the coroutine is started.  When the coroutine completes,
the awaiting coroutine is resumed via symmetric transfer, and the return value
or exception is propagated to the caller.

The result type of the task is the type parameter to task; the default is void.  

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

== resume_result.h ==

There are situations where it is useful to know whether a given asynchronous operation
suspended.  For example, when waiting on a lock, it can be useful to know whether the
lock wait actually resulted in a suspension so that the resuming coroutine can
decide to reschedule on a threadpool thread rather than blocking the coroutine that
released the lock.

```with_resume_result``` is a function accepting an awaitable object and returns
a coroutine whose result has two members:

```
// Determine whether with_resume_result believes the calling coroutine was suspended.
bool did_suspend() const;

// Get the result of awaiting the underlying awaitable.
auto result();
```
