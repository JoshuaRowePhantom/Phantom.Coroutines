
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

=== Implementation Notes ===

```task<Result>``` stores its return value in the task object itself and releases
the promise object as soon as the task's awaiter is resumed.  Thus, promises
that embody a large amount of state will be released quickly, and the task's
state does not bloat the promise state.
