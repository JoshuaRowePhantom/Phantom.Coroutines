# [Phantom.Coroutines](../README.md)

## ```sync_wait.h```

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
