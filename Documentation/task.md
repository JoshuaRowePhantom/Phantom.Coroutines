# [Phantom.Coroutines](../README.md)

## ```task.h```

Task.h provides an extensible ```task<Result>``` implementation for implementing lazily-started coroutines
that have a single awaiter.  

This implementation is particularly inexpensive, and doesn't even use atomic operations.
The only supported operation on a task is to move it and to co_await it once.
Upon co_await'ing the task, the coroutine is started.  When the coroutine completes,
the awaiting coroutine is resumed via symmetric transfer, and the return value
or exception is propagated to the caller.

The result type of the task is an rvalue reference to the type parameter to ```task<Result>``` 
unless the task returns void.  This is done to permit using the result of a task with no additional
copying.

The default return type of the task is void, so a typical usage is:

```
task<> DoSomethingThatDoesntReturnAnything() { co_return; }
```

## ```task<typename Result = void>```

```task<Result>``` is an alias for ```basic_task<task_promise<Result>>```. 
```basic_task<Promise>```.

## [```task_promise<typename Result, is_task_promise_policy Policies...>```](#task_promise)

This alias template provides a ```basic_task_promise``` with the requested
policies applied.

## ```basic_task<typename Promise>```

```task<Result>``` is an alias for ```basic_task<task_promise<Result>>```. 
```basic_task<Promise>```.

## ```basic_task_promise<typename Result, ...>```

```basic_task_promise``` implements the behavior of a lightweight task promise.
It accepts explicitly selected policies. Typically, users extending ```task```
should extend ```task_promise<...>```, as its type parameters are documented.

## Extending tasks

### Policy selection

It is possible to use non-default policies to the ```task``` classes without 
performing explicit extension. The typical way to do so is to declare an alias
template:

```c++
class other_promise{};

template<typename Result = void>
using waited_on_by_other_promise_task_type 
= 
basic_task<
    task_promise<
        continuation_type<std::coroutine_handle<other_promise>>
    >
>;
```

Now, ```waited_on_by_other_promise_task_type``` can be used like a ```task<>```:

```c++
task<> OtherFunction();

waited_on_by_other_promise_task_type<int> MyFunction()
{
    co_await OtherFunction();
    co_return 6;
}
```

### Extension

```task<>``` is backed by the extension mechanisms in []```extensible_promise.h```](extensible_promise.md).


### Implementation Notes

```task<Result>``` stores its return value in the awaiter for the task and releases
the promise object as soon as the task's awaiter is resumed.  Thus, promises
that embody a large amount of state will be released quickly, and the lifetime
of the result value does not negatively impact the amount of allocated memory.
