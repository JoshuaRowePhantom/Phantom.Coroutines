[!INCLUDE [Header](header.md)]

# ```policies.h```

```policies.h``` defines policies for customizing the behavior of other classes
in Phantom.Coroutines. Each policy can be used in the type argument list of a class.
Only the first matching policy is used: others are ignored. 

For example:

```
// async_mutex<> uses await_is_not_cancellable by default.
async_mutex<> awaitIsNotCancellableMutex;

// Uses await_is_cancellable
async_mutex<await_is_cancellable> awaitIsCancellableMutex;


// Uses await_is_not_cancellable
async_mutex<await_is_not_cancellable, await_is_cancellable> awaitIsCancellableMutex;

// Uses await_is_cancellable, single_awaiter, fail_on_destroy_with_awaiters
using my_single_awaiter_mutex = async_mutex<
    await_is_cancellible,
    single_awaiter,
    fail_on_destroy_with_awaiters
>;
```

## ```await_cancellation_policy```

```await_cancellation_policy``` is the base class of policies that define
how to handle destroyed awaiters. The default for most awaitable types is
```await_is_not_cancellable```, as this is usually the highest performing
option. 

### ```await_is_not_cancellable```

Use ```await_is_not_cancellable``` to specify that all co_await operations must
either complete or the awaitable object itself be destroyed. There is no
way to cancel an outstanding wait operation. If the awaiter of a ```co_await```
object is destroyed, the program must make sure that the awaitable object
itself is destroyed without ever attempting to signal an awaiter, otherwise
undefined behavior results.  

Using ```await_is_not_cancellable``` is generally higher-performing than ```await_is_cancellable```,
as most classes are optimized to use lock-free programming.

### ```await_is_cancellable```

Use ```await_is_cancellable``` to specify that a co_await operation can be
cancelled by destroying the awaiter object returned from the co_await operation.

Using ```await_is_cancellable``` usually requires the awaitable object to acquire
locks to remove waiters from cancellation lists for either cancellation or
signalling, so usually has worse performance than ```await_is_not_cancellable```.

## ```awaiter_cardinality_policy```

Cardinality policies allow customizing whether an awaitable object can
have multiple simultaneous ```co_await``` operations outstanding. 

### ```single_awaiter```

Use ```single_awaiter``` to indicate that only a single ```co_await``` 
operation is permitted to be outstanding at one time.

Attempting to ```co_await``` an awaitable object twice will result in undefined
behavior. Debug builds will typically assert.

```single_awaiter``` typically allows allocating slightly less memory
per awaiter and may have other performance benefits. It is therefore the
highest performing option. However, the necessity to ensure there is only
one awaiter can complicate a program.

### ```multiple_awaiters```

Use ```multiple_awaiters``` to indicate that multiple ```co_await``` 
operations are permitted to be outstanding at one time. ```multiple_awaiters```
typically requires linked list implementations of awaiters, and thus requires
slightly more memory per awaiter and a few more instructions per operation
to maintain the list. 

## ```await_result_on_destruction_policy```

The ```await_result_on_destruction_policy``` selects a behavior for what should
happen to awaiters when the awaitable object is destroyed.

### ```throw_on_destroy```

Using ```throw_on_destroy``` causes the awaiters of an awaitable object to receive
an exception:

```
throw std::future_error(
		std::future_errc::broken_promise);
```

This policy allows destroying an awaitable object to terminate all the awaiters on it
by signalling an exception.

Note that the application must resolve the race condition between destroying the
awaitable object and awaiting the awaitable object via other means.

### ```noop_on_destroy```

```noop_on_destroy``` causes the destructor of an awaitable object to do nothing
when the awaitable object is destroyed. This is usually the highest performing
option.

Note that the application must resolve the race condition between destroying the
awaitable object and awaiting the awaitable object via other means.

### ```fail_on_destroy_with_awaiters```

```fail_on_destroy_with_awaiters``` causes the destructor of an awaitable object
to assert() in debug builds if there are any awaiters. This policy has the
same performance characteristics of ```noop_on_destroy``` for release builds.

Note that the application must resolve the race condition between destroying the
awaitable object and awaiting the awaitable object via other means.

## ```continuation_type<is_continuation>```

The ```continuation_type<is_continuation>``` policy allows specifying the type of continuation
the awaitable object stores. Usually, most applications use ```std::coroutine_handle<>```
as the continuation type. An application may prefer to use
a promise-specific ```std::coroutine_handle<Promise>``` type or even any other class that
obeys the [```is_continuation```](type_traits.md#is_continuation) semantics.

