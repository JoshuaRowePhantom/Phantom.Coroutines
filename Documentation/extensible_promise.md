# [Phantom.Coroutines](../README.md)

## ```extensible_promise.h```

```extensible_promise.h``` contains the classes that enable building extensible
promise and future types. Extensible promises are promises types that are
aware they may be extended, and do not attempt to access coroutine handles
or promise objects directly except through the schemes documented in this page.

The C++ standard requires that std::coroutine_handle instances
are acquired via the _precise_ type of the Promise object. See
[Lewis Baker's explanation](https://lewissbaker.github.io/2017/11/17/understanding-operator-co-await):

 > The ```coroutine_handle<P>::from_promise(P& promise)``` function allows reconstructing the coroutine handle from a reference to the coroutine’s promise object. Note that you must ensure that the type, P, exactly matches the concrete promise type used for the coroutine frame; attempting to construct a ```coroutine_handle<Base>``` when the concrete promise type is ```Derived``` can lead to undefined behaviour.

Extensible promises should use deduced explicit object parameters for most
methods, and parameter return types that need to refer to the promise object
by using the deduced type. For example:

```c++
class my_promise :
    public extensible_promise
{
public:
    template<
        // Uses a type parameter here,
        // instead of assuming the promise is
        // a my_promise.
        typename Promise
    >
    class my_initial_suspend_awaiter :
        public extensible_awaitable<Promise>
    {
        my_initial_suspend_awaiter(
            Promise&
        );

        bool await_ready(
            // explicit object parameter
            this auto& self
        )
        {
            return false;
        }
    }

    auto initial_suspend(
        // explicit object parameter
        this auto& self
    )
    {
        return my_initial_suspend_awaiter
        {
            self
        };
    }
};
```

### [```extensible_promise```](#extensible_promise)

An ```extensible_promise``` is a promise type that can
be extended or wrapped by other promise types.

```c++
class extensible_promise
{
public:
    // Get the coroutine handle for the promise object.
    auto handle(
        this auto& self
    ) noexcept;
};

template<
    typename T
> concept is_extensible_promise =
std::derived_from<T, extensible_promise>;
```

### [```extensible_awaitable```](#extensible_awaitable)

An ```extensible_awaitable<typename Promise>``` object is an awaitable object
that refers to a promise. The reference is stored internally as
a [```std::coroutine_handle<Promise>```](https://en.cppreference.com/w/cpp/coroutine/coroutine_handle), so that the compiler can perform optimizations ensuring
that the pointer to the promise does not escape.

The following members are provided:

```c++
// An extensible awaitable is an awaitable object that can reference
// an extensible promise.
template<
    typename Promise
> class extensible_awaitable
{
public:
    using promise_type = Promise;
    using coroutine_handle_type = coroutine_handle<promise_type>;

protected:
    // Construct using a reference to the promise.
    extensible_awaitable(
        Promise& promise
    );

    // Construct using a handle to the promise.
    extensible_awaitable(
        coroutine_handle_type coroutineHandle = nullptr
    );

    // Get a reference to the handle to the promise.
    // The reference is non-const if self is non-const.
    decltype(auto) handle(
        this auto& self);

    // Get a reference to the underlying promise.
    promise_type& promise() const;

public:
    // Return true if this instance's handle() is a valid handle.
    operator bool() const noexcept;

    // Compare two instance by using the handle()'s value.
    friend auto operator <=> (
        const extensible_awaitable<Promise>&,
        const extensible_awaitable<Promise>&
        ) noexcept = default;
};
```

### [```extended_awaiter```](#extended_awaiter)

```extended_awaiter``` is a base class for an awaiter that extends
another [```is_awaitable```](type_traits.md#is_awaitable) object and
refers to a Promise object. The awaitable 
object is wrapped using [```awaiter_wrapper```](awaiter_wrapper.md),
and the promise is wrapped using ```extensible_awaitable```.
The awaiter, promise object, and promise handle objects are all available
as protected methods:

```c++
template<
    typename Promise,
    is_awaitable Awaitable
> 
class extended_awaiter<
    Promise,
    Awaitable
>
    :
    public extensible_awaitable<Awaitable>,
    public awaiter_wrapper<Awaitable>
{
public:
    // Construct 
    template<
        typename AwaitableArg
    >
    extended_awaiter(
        Promise& promise,
        AwaitableArg&& awaitable
    );

    template<
        typename AwaitableArg
    >
    extended_awaiter(
        coroutine_handle<Promise> promiseHandle,
        AwaitableArg&& awaitable
    );

protected:
    // Get the promise handle, via extensible_awaitable
    std::coroutine_handle<Promise> handle(
        this auto& self
    );

    // Get the promise, via extensible_awaitable
    Promise& promise(
        this auto& self
    );

    // Get the awaiter, via awaiter_wrapper
    auto& awaiter(
        this auto& self
    );
};
```

### [```derived_promise```](#derived_promise)

Users can derive from ```derived_promise<BasePromise>```
to extend another promise type. This provides "is-a" relationships
between promise objects.

```derived_promise<BasePromise>``` provides some helpers to aid
implementers deriving from an unknown promise type. The ```BasePromise``` 
type argument satisfies ```is_extensible_promise```,
so it is guaranteed the [```extensible_promise```](#extensible_promise)
methods are available. 

#### Construction
```derived_promise``` provides
a constructor that accepts all arguments. This constructor either
delegates to the default constructor or to a constructor that
accepts the arguments. This makes it possible to write a
wrapper-type promise that uses the arguments and delegates to an 
underlying promise type without having determine to whether the underlying promise
itself uses the arguments. 

The usual options for writing a constructor in a derived_promise are
to inherit the constructor with the ```using``` keyword or to delegate
to the base constructor.

```c++
template<typename Promise>
class InheritingConstructorPromise : public derived_promise<Promise>
{
using derived_promise<Promise>::derived_promise;
};

template<typename Promise>
class ArgumentTracingPromise : public derived_promise<Promise>
{
    void Trace(
        const auto& value
    )
    {
        std::cerr << value << "\n";
    }

public:
    ArgumentTracingPromise(
        auto && ... args
    ) : derived_promise<Promise>::derived_promise
    {
        // Trace all the argument values
        // before forwarding them.
        std::forward<decltype(args)>((Trace(args), args))...
    }
    {
    }
};
```

#### await_transform

```derived_promise``` also ensures there is always an implementation
of ```await_transform```. If the underlying promise provides an
```await_transform``` method, then the ```derived_promise``` inherits
it directly via the ```using``` keyword. Otherwise, one is synthesized
that does nothing to the argument. The purpose of this is to make it
easy to write delegating ```await_transform```.

#### Formal specification

```c++
template<
    is_extensible_promise BasePromise
> class derived_promise
{
protected:
    using base_promise_type = BasePromise;
    
public:
    // There is always a constructor that accepts the full
    // argument list. Its implementation either delegates
    // to the underlying constructor or invokes
    // the default constructor.
    template<
        typename ... Args
    > derived_promise(
        Args&&... args
    );

    // There is always an await_transform method available,
    // either from the BasePromise or from derived_promise,
    // with the intent that it is easy to delegate
    // await_transform calls to the base promise object.
    decltype(auto) await_transform(
        auto&& awaitable
    ) noexcept;
};
```
