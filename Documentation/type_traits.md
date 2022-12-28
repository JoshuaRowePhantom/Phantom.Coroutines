# [Phantom.Coroutines](../README.md)

## type_traits.h

This file contains concepts and structures to help with template metaprogramming.

### [```is_awaitable```](#is_awaitable)

Tests to see if a type can be co_await'ed, either because it has 
an operator co_await, or is an awaiter itself.
All [```is_awaiter```](type_traits.md#is_awaitable) objects
are also ```is_awaitable```, so that the ```is_awaitable``` and ```is_awaiter```
concepts can be used as expected:

* A template can accept ```is_awaitable``` objects to provide generic behavior.
* A template can specialize for ```is_awaiter``` objects to provide specific behavior
  for awaiters.

```c++
template<
    typename TAwaitable
> concept is_awaitable;
```

### [```is_awaiter```](#is_awaiter)

Tests to see if a type is an awaiter, meaning it has the await_ready,
await_suspend, and await_resume methods.
```c++
template<
    typename TAwaiter
>
concept is_awaiter;
```

### [```has_co_await```](#has_co_await)

Tests to see if a type has an awaiter-returning operator co_await.
The operator co_await can be a member or non-member.
```c++
template<
    typename TAwaitable
> concept has_co_await;
```

### [```has_co_await_member```](#has_co_await_member)

Tests to see if a type has an awaiter-returning member operator co_await.
```c++
template<
    typename TAwaitable
> concept has_co_await_member;
```

### [```has_co_await_non_member```](#has_co_await_non_member)

Tests to see if a type has an awaiter-returning non-member operator co_await.
```c++
template<
    typename TAwaitable
> concept has_co_await_non_member;
```

### [```awaitable_result_type```](#awaitable_result_type)

Get the result type of a co_await'able object, as the ```type``` member.
This is equivalent to the return type of the await_resume method,
and may be a reference or r-value reference type.
```
template<
    is_awaitable TAwaitable
>
struct awaitable_result_type;
```

### [```awaitable_result_type_t```](#awaitable_result_type_t)

Get the result type of co_await'able object.
This is equivalent to the return type of the await_resume method,
and may be a reference or r-value reference type.
```c++
template<
    is_awaitable TAwaitable
>
using awaitable_result_type_t = awaitable_result_type<TAwaitable>::type;
```

### [```get_awaiter```](#get_awaiter)

Given an [```is_awaitable```](type_traits.md#is_awaitable) object,
get an [```is_awaiter```](type_traits.md#is_awaiter) object that implements
the ```await_ready```, ```await_suspend```, and ```await_resume``` methods.

For [```is_awaiter```](type_traits.md#is_awaiter) objects, the return
type is either an l-value or r-value reference to the original object.

For [```has_co_await```](type_traits.md#has_co_await) objects,
the return type is exactly the return type of ```operator co_await```.
