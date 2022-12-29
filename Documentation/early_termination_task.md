# [Phantom.Coroutines](../README.md)

## ```early_termination_task.h```

### ```early_termination_task```

```early_termination_task``` provides facitilies to terminate a coroutine
before its normal termination, potentially returning a value indicating
this termination.

C++ dialects aim to make exception throwing and catching as inexpensive
as possible, but few implementations are able to achieve the efficiency
of ordinary return value semantics. This, unfortunately, often leads to
code and runtime inefficiency of successful execution, due to the
need to write ```if (error) { return; }``` statements after every operation
that could fail. This litters the code with such checks, and adds additional
conditional branch instructions to the instruction stream.

```early_termination_task``` provides a framework for eliminating these
efficiencies by providing these features:

1. The ability to ```co_await``` an arbitrary type to check that it contains an error.
2. The ability to ```co_await``` an ```early_termination_task``` that itself is parameterized on an error type.
3. Upon detection of an error, resuming the inner most error handler for that error.
4. The ability to ```co_await``` an ```early_termination_task``` and specify that the wait operation is an error handler, thus being a valid target for #3.
5. The ability to handle thrown exceptions by translating them in the same way.
6. The ability to translate errors and exceptions into an appropriate result of callers of an ```early_termination_task```.

These mechanisms imply that the ```co_await``` expressions in such a coroutine
may suspend a coroutine and resume a _calling_ coroutine _without_ throwing an exception;
the resumption of the caller will typically result in the _destruction_ of the coroutine
so suspended. This means that try / catch error handling will not work, and RAII based
releasing of resources is to be used at all times.

The types of ordinary results, of errors to handle,
and of the means to report errors are specified in the template parameters to
```early_termination_task```. 

```early_termination_task``` is built using the semantics of 
[```task```](task.md). An ```early_termination_task``` can only be awaited
once as an r-value and cannot be copied.

An example use would be:

```c++
template<
    typename Value = void
>
using error_task = early_termination_task<
    Value,
    std::expected<
        Value, 
        std::error_condition
    >,
    expected_early_termination_handler,
    error_condition_early_termination_transformer
>;

error_task<int> MyErrorReturningCoroutine()
{
    co_return std::unexpected { std::make_error_condition(std::errc::bad_address) };
}

error_task<int> MySuccessfulCoroutine()
{
    co_return 5;
}

error_task<int> MyOuterCoroutine()
{
    return
        // This co_await will succeed
        co_await MySuccessfulCoroutine()
        // This co_await will fail, and will resume the caller
        // of MyOuterCoroutine.
        + co_await MyErrorReturningCoroutine();
}

error_task<int> MyErrorHandlingCoroutine()
{
    auto result = co_await MyOuterCoroutine().result();
    static_assert(
        std::same<
            std::expected<int, std::error_condition>, 
            decltype(result)>);

    // If the error was bad_address,
    // just return 0.
    if (result == std::make_error_condition(std::errc::bad_address))
    {
        co_return 0;
    }

    // Otherwise, return the result value or the original error.
    co_return co_await result;
}
```

The type arguments to ```early_termination_task``` are:

* The type of the value returned by non-handling co_await operations.
* The type of the value returned by error-handling co_await operations.
* The [policies](policies.md) and type handlers to apply to the ```early_termination_task```, in precedence order.

For convenience, it is useful to user that handlers and reporters
follow an implementation and naming convention matching that used
by the library itself. 

* \<error-type>_early_termination_transformer

  Implements the behavior of determining that a given type should
  terminate a coroutine.

* \<error-type>\_as_\<result-type>_early_termination_result

  Implements the behavior that a given type should be reported as
  a particular result value to error handlers.

* <result-type>_early_termination_result

  Implements the behavior that all results should be reported
  as a particular result value to error handlers.

* \<error-type>\_as_\<result-type>_early_termination_result

  Implements the behavior that a given type should be reported as
  a particular result value.

* \<error-type>\_as_\<result-type>_early_termination_handler

  Combines the behavior of:
    * \<error-type>_early_termination_transformer
    * \<error-type>\_as_\<result-type>_early_termination_result

An ```early_termination_transformer``` type derives from the class
```early_termination_transformer```, and is expected to provide
an implementation of ```await_transform``` that transforms
the handled result type with an ```early_termination_awaiter``-derived
awaiter.

An ```early_termination_result``` type derives from the class
```early_termination_result```, and is expected to provide
an implementation of ```resume(T&&)``` that is used to resume
the calling coroutine.

An ```early_termination_handler``` type simply derives
from both the ```early_termination_checker``` and 
```early_termination_result``` classes to provide compound behavior.

The default behavior for exception is as follows:

* An exception thrown by coroutine is caught by the ```early_termination_promise```
  via its ```unhandled_exception()``` method.
* The exception is "tunnelled" through all the non-handling ```early_termination_task```
  tasks being awaited until either the top level task is reached or 
  an error-handling await operation is encountered.
* The exception is then rethrown into that coroutine.

### ```early_termination_transformer```

This class acts as the base class for transformers that look at
a particular error type.

### ```early_termination_awaiter```

This class is the base class for awaiters that handle a particular
error type.

### ```early_termination_result```

This class is the base class for transforming a result into a
value returned to an error handling coroutine.

## Supporting type-specific header files

### [```expected_early_termination.h```](#error_condition_early_termination)

This file provides ```early_termination_task``` behavior to handle
```std::expected``` instances. Any ```std::expected``` whose 
[```operator bool```](https://en.cppreference.com/w/cpp/utility/expected/operator_bool)
returns false is considered to be an error

The classes provided are:

* ```expected_early_termination_transformer```

  Performs ```co_await``` transformations to detect errors on an ```std::expected```
  instance.

* ```expected_early_termination_result```

  Transforms errors into ```std::expected``` instance as necessary.

* ```expected_early_termination_handler```

  Combines the behavior of ```expected_early_termination_result``` and
  ```expected_early_termination_transformer```.

### [```error_condition_early_termination.h```](#error_condition_early_termination)

This file provides ```early_termination_task``` behavior to handle
```std::error_condition``` instances. Any ```std::error_condition```
whose [```operator bool```](https://en.cppreference.com/w/cpp/error/error_condition/operator_bool) 
returns true is considered to be an error.

The classes provided are:

* ```error_condition_early_termination_transformer```

  Performs ```co_await``` transformations to detect errors on an ```std::error_condition```
  instance.

