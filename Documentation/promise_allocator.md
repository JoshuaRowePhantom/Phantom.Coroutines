# [Phantom.Coroutines](../README.md)

## ```promise_allocator.h```

```promise_allocator.h``` provides support for using custom allocators
to allocate the memory for promise objects.

To use a custom allocator for an extensible promise type, use promise_allocator
to derive from the promise type. Any promise function invocation that
has an allocator argument will use the allocator provided, otherwise
the default allocator will be used if the allocator can be default-constructed.

For example, to use the ```std::pmr::polymorphic_allocator``` as the allocator,
one might use:

```c++
template<
    typename Promise
> using polymorphic_allocator_promise = 
    promise_allocator<
        Promise, 
        std::pmr::polymorphic_allocator<>
    >;

template<
    typename Result = void
> using pmr_task = 
basic_task<
    polymorphic_allocator_promise<
        task_promise<Result>>>;

pmr_task<> promise_that_uses_allocator(
    polymorphic_allocator<> allocator,
    int otherArgument
)
{
    co_return otherArgument * otherArgument;
}

task<> call_promise_that_uses_allocator()
{
    polymorphic_allocator<> allocator;
    co_await promise_that_uses_allocator(allocator, otherArgument);
}
```

If the base promise class has a ```get_return_object_on_allocation_failure```
method, then the promise_allocator will catch std::bad_alloc exceptions
and return a nullptr value from the allocation attempt, triggering
the compiler's ability to call ```get_return_object_on_allocation_failure```.
