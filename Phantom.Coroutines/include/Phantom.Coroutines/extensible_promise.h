#pragma once

#include <concepts>
#include <type_traits>
#include "type_traits.h"
#include "awaiter_wrapper.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{

// An extensible_promise is a promise type that can
// be extended or wrapped by other promise types.
class extensible_promise
{
public:
    auto handle(
        this auto& self
    ) noexcept
    {
        return std::coroutine_handle<
            std::remove_cvref_t<decltype(self)>
        >::from_promise(self);
    }
};

template<
    typename T
> concept is_extensible_promise =
std::derived_from<T, extensible_promise>;

template<
    typename ExtendedPromise,
    typename Promise
> concept is_extended_promise_of = 
is_extensible_promise<Promise>
&& is_extensible_promise<ExtendedPromise>
&& requires(ExtendedPromise promise)
{
    { promise.template promise<Promise>() } -> std::same_as<Promise&>;
};

template<
    typename Promise
> struct wrapper_promise_return
{
    decltype(auto) return_value(
        this auto& self,
        auto&&... value
    )
    {
        return self->return_value(
            std::forward<decltype(value)>(value)...);
    }
};

template<
    has_return_void Promise
> struct wrapper_promise_return<
    Promise
>
{
    decltype(auto) return_void(
        this auto& self,
        auto&&... value
    )
    {
        return self->return_void(
            std::forward<decltype(value)>(value)...);
    }
};

// The template derived_promise_await_transform ensures there is a valid
// await_transform() method in the derived_promise implementation,
// so that it can always be called unconditionally by derived classes.
template<
    typename BasePromise
> class derived_promise_await_transform
{
public:
    decltype(auto) await_transform(
        auto&& awaitable
    ) noexcept
    {
        return std::forward<decltype(awaitable)>(awaitable);
    }
};

template<
    typename BasePromise
> requires has_await_transform<BasePromise>
class derived_promise_await_transform<
    BasePromise
>
{
public:
};

// A derived_promise is a promise that wraps an extensible_promise
// by derivation.
template<
    is_extensible_promise BasePromise
> class derived_promise
    :
    public BasePromise,
    public derived_promise_await_transform<BasePromise>
{
    struct BasePromiseTag {};
protected:
    typedef BasePromise base_promise_type;

    decltype(auto) base_promise()
    {
        return *this;
    }

public:
    // These constructors allow the derived promise
    // to always provide a constructor and delegate to
    // derived_promise's constructor,
    // without regard as to whether the base promise
    // provides a constructor.
    // 
    // A derived promise can also use a using declaration
    // to import derived_promise's constructors.

    // Enable construction by delegating the arguments
    // to the promise object.
    // This constructor is enabled only if the promise object
    // supports the argument set.
    template<
        typename ... Args
    > derived_promise(
        Args&&... args
    )
        requires std::constructible_from<BasePromise, Args&&...>
    :
    BasePromise(
        std::forward<Args>(args)...
    )
    {}

    // Enable construction by invoking the default constructor.
    // This constructor is enabled only if the promise object
    // does not support the argument set and default-constructs
    // the promise.
    template<
        typename ... Args
    > derived_promise(
        Args&&... args
    ) requires 
        !std::constructible_from<BasePromise, Args&&...>
        && std::constructible_from<BasePromise>
    :
    BasePromise()
    {}
};

// An extensible awaitable is an awaitable object that can reference
// an extensible promise.
template<
    typename Promise
> class extensible_awaitable
{
    template<
        typename Promise,
        is_awaitable Awaitable
    > friend class extended_awaiter;

public:
    using promise_type = Promise;
    using coroutine_handle_type = coroutine_handle<promise_type>;

private:
    coroutine_handle<promise_type> m_coroutineHandle;

protected:
    extensible_awaitable(
        Promise& promise
    ) :
        m_coroutineHandle{ coroutine_handle_type::from_promise(promise) }
    {}

    extensible_awaitable(
        coroutine_handle_type coroutineHandle = nullptr
    ) :
        m_coroutineHandle { coroutineHandle }
    {}

    decltype(auto) handle(
        this auto& self)
    {
        return (self.m_coroutineHandle);
    }

    promise_type& promise() const
    {
        return m_coroutineHandle.promise();
    }

public:
    operator bool() const noexcept
    {
        return handle().operator bool();
    }

    friend auto operator <=> (
        const extensible_awaitable<Promise>&,
        const extensible_awaitable<Promise>&
        ) noexcept = default;
};

template<
    typename Awaitable
> constexpr bool is_extensible_awaitable_v = false;

template<
    typename Promise
> constexpr bool is_extensible_awaitable_v<
    extensible_awaitable<Promise>
> = true;

template<
    typename Awaitable
> concept is_extensible_awaitable = is_extensible_awaitable_v<Awaitable>;

template<
    typename Awaitable,
    typename Promise
> concept is_extensible_awaitable_for =
is_extensible_awaitable<Awaitable>
&& std::derived_from<Awaitable, extensible_awaitable<Promise>>;

template<
    typename Promise,
    is_awaitable Awaitable
> class extended_awaiter;

template<
    typename Awaitable,
    typename Promise
> constexpr bool is_extended_awaiter_v = false;

template<
    typename Promise,
    is_awaitable BaseAwaitable
> constexpr bool is_extended_awaiter_v<
    extended_awaiter<Promise, BaseAwaitable>,
    Promise
> = true;

template<
    typename Awaitable,
    typename Promise
> concept is_extended_awaiter = is_extended_awaiter_v<Awaitable, Promise>;

template<
    typename Promise,
    is_awaitable Awaitable
> class extended_awaiter
    :
public awaiter_wrapper<Awaitable>,
public extensible_awaitable<Promise>
{
    template<
        typename Promise,
        is_awaitable Awaitable
    > friend class extended_awaiter;

public:

    template<
        std::invocable AwaitableFunc
    >
    extended_awaiter(
        Promise& promise,
        AwaitableFunc&& awaitableFunc
    ) noexcept(
        noexcept(awaiter_wrapper<Awaitable>{ std::forward<AwaitableFunc>(awaitableFunc) })
        )
        :
        awaiter_wrapper<Awaitable>{ std::forward<AwaitableFunc>(awaitableFunc) },
        extensible_awaitable<Promise>{ promise }
    {}

    template<
        std::invocable AwaitableFunc
    >
    extended_awaiter(
        coroutine_handle<Promise> promiseHandle,
        AwaitableFunc&& awaitableFunc
    ) noexcept(
        noexcept(awaiter_wrapper<Awaitable>{ std::forward<AwaitableFunc>(awaitableFunc) })
        )
        :
        awaiter_wrapper<Awaitable>{ std::forward<AwaitableFunc>(awaitableFunc) },
        extensible_awaitable<Promise>{ promiseHandle }
    {}

protected:
    using extensible_awaitable<Promise>::handle;
    using extensible_awaitable<Promise>::promise;
};

// This specialization uses the extensible awaitable object's handle() method
// to retrieve the handle, instead of storing the handle directly,
// thus optimizing an extended_awaiter wrapping another extended_awaiter.
template<
    typename Promise,
    is_awaitable Awaitable
> 
requires is_extensible_awaitable_for<awaiter_type<Awaitable>, Promise>
class extended_awaiter<
    Promise,
    Awaitable
>
    :
    public awaiter_wrapper<Awaitable>
{
    template<
        typename Promise,
        is_awaitable Awaitable
    > friend class extended_awaiter;

public:

    template<
        typename AwaitableArg
    >
    extended_awaiter(
        Promise& promise,
        AwaitableArg&& awaitable
    ) :
        // Delegate to awaiter_wrapper
        awaiter_wrapper<Awaitable>{ std::forward<AwaitableArg>(awaitable) }

        // Discard the "promise" argument, since it will have been stored
        // in the target awaiter.
    {}

    template<
        typename AwaitableArg
    >
    extended_awaiter(
        coroutine_handle<Promise> promiseHandle,
        AwaitableArg&& awaitable
    ) :
        // Delegate to awaiter_wrapper
        awaiter_wrapper<Awaitable>{ std::forward<AwaitableArg>(awaitable) }

        // Discard the "promise" argument, since it will have been stored
        // in the target awaiter.
    {}

protected:
    std::coroutine_handle<Promise> handle(
        this auto& self
    ) noexcept
    {
        return self.awaiter().handle();
    }

    Promise& promise(
        this auto& self
    ) noexcept
    {
        return self.awaiter().promise();
    }
};

}

using detail::extensible_promise;
using detail::is_extensible_promise;
using detail::extensible_awaitable;
using detail::extended_awaiter;
using detail::derived_promise;

}
