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

