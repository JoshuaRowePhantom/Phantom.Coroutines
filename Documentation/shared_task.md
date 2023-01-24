# [Phantom.Coroutines](../README.md)

## ```shared_task.h```


```shared_task.h``` provides an extensible ```shared_task<Result>``` implementation for implementing lazily-started coroutines
that have can have multiple awaiters and can be copied and moved.


The result type of the task is a value reference to the type parameter to ```task<Result>``` 
unless the task returns void.  

The default return type of the task is void, so a typical usage is:

```
shared_task<> DoSomethingThatDoesntReturnAnything() { co_return; }
```


## ```shared_task<typename Result = void>```

```shared_task<Result>``` is an alias for ```basic_shared_task<shared_task_promise<Result>>```. 

## [```shared_task_promise<typename Result, is_shared_task_promise_policy Policies...>```](#shared_task_promise)

This alias template provides a ```basic_shared_task_promise``` with the requested
policies applied.

## ```basic_shared_task<typename Promise>```

```shared_task<Result>``` is an alias for ```basic_shared_task<shared_task_promise<Result>>```. 

## ```basic_shared_task_promise<typename Result, ...>```

```basic_shared_task_promise``` implements the behavior of a shared task promise.
It accepts explicitly selected policies. Typically, users extending ```shared_task```
should extend ```shared_task_promise<...>```, as its type parameters are documented.

## Extending shared tasks

### Policy selection

It is possible to use non-default policies to the ```shared_task``` classes without 
performing explicit extension. The typical way to do so is to declare an alias
template:

```c++
class other_promise{};

template<typename Result = void>
using waited_on_by_other_promise_task_type 
= 
basic_shared_task<
    shared_task_promise<
        continuation_type<std::coroutine_handle<other_promise>>
    >
>;
```

Now, ```waited_on_by_other_promise_task_type``` can be used like a ```shared_task<>```:

```c++
task<> OtherFunction();

waited_on_by_other_promise_task_type<int> MyFunction()
{
    co_await OtherFunction();
    co_return 6;
}
```

### Extension

```shared_task<>``` is backed by the extension mechanisms in []```extensible_promise.h```](extensible_promise.md).

