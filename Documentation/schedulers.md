# [Phantom.Coroutines](../README.md)

## ```scheduler.h```

Schedulers implement the following concept:

```
template<
	typename T
> concept is_scheduler = requires (T t)
{
	{ t.schedule() } -> is_awaitable;
};
```

Phantom.Coroutines comes with two scheduler implementation and one wrapper: 
 * ```inline_scheduler``` 
 * ```thread_pool_scheduler```
 * ```static_thread_pool```

## ```inline_scheduler.h```

```inline_scheduler``` implements the ```is_scheduler``` concept by never suspending,
i.e. returning ```std::never_suspend{}```. ```inline_scheduler``` is useful mostly for testing.

## ```thread_pool_scheduler.h```

```thread_pool_scheduler``` implements a high-performance work-stealing mostly lock-free implementation
of a scheduler. The ```thread_pool_scheduler``` exposes a ```scheduler``` method that returns
an awaitable, and a ```process_items``` method that a caller can use to process items on that thread
until the ```std::stop_signal``` parameter is signalled.

The typical use case is to not use ```thread_pool_scheduler``` directly, but instead to use
```static_thread_pool```.

## ```static_thread_pool.h```

```static_thread_pool``` wraps ```thread_pool_scheduler``` and provides a fixed-size pool
of threads to perform processing of work items. It can be stopped by calling the ```shutdown``` method
or by destroying it.
