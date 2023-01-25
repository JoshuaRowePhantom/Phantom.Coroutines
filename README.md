# Phantom.Coroutines

A C++23 coroutine library.

## Goals 

This is effort, much inspired by Lewis Baker's [cppcoro library](https://github.com/lewissbaker/cppcoro), is an ab-initio
set of C++ classes designed to implement coroutines with great efficiency and
flexibility.  This implementation is intended to work _only_ on compilers
with the latest and greatest features, especially symmetric transfer and "deduced this".

The coroutines defined by C++20 are -awesome-, but there are some non-straightforward
results from it that this library attempts to solve.  Most especially, deriving
new task / promise types from an existing library is extremely difficult.  The
```coroutine_handle<T>::from_promise``` method requires the precise type of the
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

The library also aims to support different behavior axes that are convenient for certain use cases.
It does so via [policies.h](Documentation/policies.md).

The #1 goal of the library is high performance. Most defaults are oriented towards
high performance operation. 

## Using 

Put the ```include/Phantom.Coroutines``` directory in your include path.  Then, 
```#include``` the header that you desire:

```
#include <Phantom.Coroutines/task.h>
```

The contents of the ```Phantom::Coroutines``` namespace are available for use as documented.  Everything
in ```Phantom::Coroutines::detail``` is undocumented.  At some point, this will be
enforced through C++ modules.

Many classes make use of [policies](Documentation/policies.md) to customize behavior, while providing
default high-performance policies for typical uses. 

Library contents:

### [```async_auto_reset_event.h```](Documentation/async_auto_reset_event.md)

Auto reset event.

### [```async_generator.h```](Documentation/async_generator.md)

Async generator.

### [```async_manual_reset_event.h```](Documentation/async_manual_reset_event.md)

Manual reset event.

### [```async_mutex.h```](Documentation/async_mutex.md)
   
Mutual exclusion inside coroutines.

### [```async_promise.h```](Documentation/async_promise.md)
   
Delayed acquisition of values.

### [```async_scope.h```](Documentation/async_scope.md)
   
Start background tasks asynchronously and wait for them to complete.

### [```awaiter_wrapper.h```](Documentation/awaiter_wrapper.md)
   
Wrap awaitable objects with an awaiter implementation.

### [```early_termination_task.h```](Documentation/early_termination_task.md)
   
Coroutines that terminate execution when termination conditions are encountered.

### [```extensible_promise.h```](Documentation/extensible_promise.md)
   
Write promise types that can be extended or do extend other promise types.

### [```extensible_promise.h```](Documentation/generator.md)
   
Non-async generator.

### [```policies.h```](Documentation/policies.md)

Provides policy parameters to other classes, such as [async_mutex.h](Documentation/async_mutex.md). 

### [schedulers](Documentation/schedulers.md)

Schedule coroutines to resume on other threads.

### [```shared_task.h```](Documentation/shared_task.md)

A [```task<>```](Documentation/task.md)-like object that can be ```co_await```'ed
multiple times, moved, and copied.

### [```suspend_result.h```](Documentation/suspend_result.md)

Discover whether a co_await operation suspended or not.

### [```sync_wait.h```](Documentation/sync_wait.md)

Create ```std::future``` objects from awaitable objects, and synchronously
wait for the results.

### [```task.h```](Documentation/task.md)

An extremely high performance lightweight awaitable operation.  This is expected
to be one of the most commonly used classes for most code.

### [```type_traits.h```](Documentation/type_traits.md)

Metaprogramming tools for introspection of asynchronous code.

