# [Phantom.Coroutines](../README.md)

## ```async_mutex.h```

```async_mutex.h``` provides a mutual exclusion primitive optimized for
coroutines. Unlike thread-based mutual exclusion, the thread that
releases a mutex need not be the same thread that acquired the mutex.

The ```async_mutex<Policies...>``` template supports these members:

```c++
template<
    is_async_mutex_policy ... Policy
> class async_mutex
{
public:
    using lock_type = std::unique_lock<basic_async_mutex>;

    bool try_lock() noexcept;
    [[nodiscard]] lock_type try_scoped_lock() noexcept;
    
    async_mutex_lock_operation lock() noexcept;
    async_mutex_scoped_lock_operation scoped_lock() noexcept;
    void unlock() noexcept;
};
```

The typical usage is:

```
class MyClass
{
    async_mutex<> m_mutex;
    std::string m_message;

    task<> set_message_of_the_day(
        std::string message
    )
    {
        auto lock = co_await m_mutex.scoped_lock();
        m_message = std::move(message);
    }
};
```

The ```lock_type``` member is a template instantiation of ```std::unique_lock```,
and thus supports the ```unlock()``` and ```try_lock``` methods.

### Policies

```async_mutex<Policies...>``` can have [policies](policies.md) applied to it from this set:

```c++
template<
    typename T
> concept is_async_mutex_policy =
is_concrete_policy<T, await_is_not_cancellable>
|| is_await_result_on_destruction_policy<T>
|| is_awaiter_cardinality_policy<T> 
|| is_continuation_type_policy<T>;
```
