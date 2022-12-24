
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
