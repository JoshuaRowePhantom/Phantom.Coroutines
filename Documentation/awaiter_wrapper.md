# [Phantom.Coroutines](../README.md)

## ```awaiter_wrapper.h```

```awaiter_wrapper``` is a template class that enables writing wrappers
around other awaitable objects. 

```awaiter_wrapper``` can wrap any [```is_awaitable```](type_traits.md#is_awaitable)
object. An ```awaiter_wrapper``` of [```is_awaiter```](type_traits.md#is_awaiter)
directly wraps the awaiter object. An awaiter_wrapper of ```awaiter_wrapper``` of [```is_awaitable```](type_traits.md#is_awaiter) wraps the result of
calling [```get_awaiter```](type_traits.md#get_awaiter).

The ```awaiter_wrapper``` class provides members:

```c++
template<is_awaitable Awaitable>
class awaiter_wrapper
{
protected:
    // The type of the wrapper awaiter.
    typedef awaiter_type ...;

    // Get the awaiter
    awaiter_type& awaiter();

    // Construct the wrapper, using the
    // awaitable object reference.
    explicit awaiter_wrapper(
        Awaiter awaiter
    ) noexcept
        requires std::is_reference_v<Awaiter>;

    // Construct the wrapper, using the returned
    // awaitable object.
    template<
        std::invocable AwaitableFunc
    > awaiter_wrapper(
        AwaitableFunc&& awaitableFunc
    ) noexcept(...);

public:
    // await_ready, await_suspend, and await_resume
    // which forward all arguments to underlying awaiter,
    // enabled for overload resolution only if the underlying
    // awaiter supports the method call,
    // and are noexcept if the underlying method call is noexcept.
};
```

Note that the constructor of ```awaiter_wrapper``` requires an ```std::invocable```.
This is to prevent errors where non-copyable, non-movable awaiters are not supported
by derived classes. The internal member variable representing the awaiter is
initialized as the return value of a function, permitting the use of non-copyable
non-movable awaiters.

Semantics for particular specializations are as follows:

* ```awaiter_wrapper<is_awaitable>```
  
  The ```awaiter_wrapper``` stores a copy of the original awaitable
  object, and also the result of ```operator co_await``` on the 
  original object. 

  The intention is that the awaiter_wrapper ensures the lifetime
  of the awaitable object exceeds that of the awaiter.

* ```awaiter_wrapper<is_awaitable&>```,
* ```awaiter_wrapper<is_awaitable&&>```

  The ```awaiter_wrapper``` stores the result of ```operator co_await```
  on the original object. The ```awaiter_wrapper``` does **NOT** store
  any reference or copy of the original awaitable object.

  The intention is that the caller already knows that the lifetime
  of the awaitable object will exceed that of the awaiter, so no
  extra storage needs to be done. Typically, this will occur
  if the awaitable object is an xvalue in a co_await expression
  or if the awaitable object is an lvalue.

* ```awaiter_wrapper<is_awaiter>```

  The ```awaiter_wrapper``` stores the actual awaiter object.

* ```awaiter_wrapper<is_awaiter&>```,
* ```awaiter_wrapper<is_awaiter&&>```

  The ```awaiter_wrapper``` stores an l-value reference to the original
  awaiter object. The intention is that the caller is using the awaiter_wrapper
  to wrap either an l-value or an xvalue in a co_await expression.
