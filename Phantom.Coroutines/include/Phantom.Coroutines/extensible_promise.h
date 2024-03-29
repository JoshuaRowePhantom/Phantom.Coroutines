#pragma once

#include <concepts>
#include <type_traits>
#include "type_traits.h"
#include "detail/scope_guard.h"
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

// Holds the identity await_transform method implementation,
// so that it is only every specialized on each awaitable type once.
class derived_promise_identity_await_transform
{
public:
    template<
        typename Value
    >
    [[msvc::intrinsic]]
    Value&& await_transform(
        Value&& awaitable
    ) noexcept
    {
        return static_cast<Value&&>(awaitable);
    }
};

template<
    typename Base
> class derived_promise_base
    :
    public Base
{
public:
    // Enable construction by delegating the arguments
    // to the base class.
    // This constructor is enabled only if the base class
    // supports the argument set.
    template<
        typename ... Args
    > derived_promise_base(
        Args&&... args
    )
        requires std::constructible_from<Base, Args&&...>
    :
    Base(
        std::forward<Args>(args)...
    )
    {}

    // Enable construction by invoking the default constructor.
    // This constructor is enabled only if the base class
    // does not support the argument set and default-constructs
    // the base class.
    template<
        typename ... Args
    > derived_promise_base(
        Args&&...
    ) requires
        !std::constructible_from<Base, Args&&...>
        && std::constructible_from<Base>
        :
    Base()
    {}
};

// The template derived_promise_await_transform ensures there is a valid
// await_transform() method in the derived_promise implementation,
// so that it can always be called unconditionally by derived classes.
template<
    typename BasePromise,
    typename ... Bases
> class derived_promise_await_transform
    :
public derived_promise_identity_await_transform,
public derived_promise_base<BasePromise>
{
    using derived_promise_base<BasePromise>::derived_promise_base;
};

template<
    typename BasePromise,
    typename ... Bases
> requires has_await_transform<BasePromise>
|| (has_await_transform<Bases> || ...)
class derived_promise_await_transform<
    BasePromise,
    Bases...
> :
    public derived_promise_base<BasePromise>
{
public:
};

// A derived_promise is a promise that wraps an extensible_promise
// by derivation.
template<
    is_extensible_promise BasePromise,
    is_template_instantiation<std::tuple> BasesTuple,
    is_template_instantiation<std::tuple> AwaitTransformBasesTuple
> class derived_promise_impl;

template<
    is_extensible_promise BasePromise,
    typename ... Bases,
    typename ... AwaitTransformBases
> class derived_promise_impl<
    BasePromise,
    std::tuple<Bases...>,
    std::tuple<AwaitTransformBases...>
>
    :
    public derived_promise_await_transform<BasePromise, Bases...>,
    public derived_promise_base<Bases>...
{
protected:
    using base_promise_type = BasePromise;

public:
    // Enable construction by delegating the arguments
    // to the promise object.
    // This constructor is enabled only if the promise object
    // supports the argument set.
    template<
        typename ... Args
    > derived_promise_impl(
        Args&&... args
    )
        requires std::constructible_from<derived_promise_await_transform<BasePromise, Bases...>, Args&&...>
    && (std::constructible_from<derived_promise_base<Bases>, Args&&...> && ...)
    :
    derived_promise_await_transform<BasePromise, Bases...>(
        std::forward<Args>(args)...
    ),
    derived_promise_base<Bases>(
        std::forward<Args>(args)...
    )...
    {}

    using AwaitTransformBases::await_transform...;
};

template<
    is_extensible_promise BasePromise,
    typename ... Bases
>
class derived_promise :
    public derived_promise_impl<
    BasePromise,
    std::tuple<Bases...>,
    typename filter_types
    <
    has_await_transform_filter,
    derived_promise_await_transform<BasePromise, Bases...>,
    derived_promise_base<Bases>...
    >::tuple_type
    >
{
    using derived_promise::derived_promise_impl::derived_promise_impl;
};

template<
    typename Promise
> class extensible_promise_handle;

template<
    typename PromiseHandle
> class extended_promise_handle;

// Detect is a type is an extensible awaitable.
template<
    typename PromiseHandle
> concept is_extensible_promise_handle = 
is_derived_instantiation<
    PromiseHandle,
    // We check for extended_promise_handle because all extensible_promise_handle
    // objects derived from extended_promise_handle, and all extended_promise_handle
    // objects support extension.
    extended_promise_handle
>;

// Detect is a type is an extensible awaiter.
template<
    typename PromiseHandle
> concept is_extensible_awaiter =
is_awaiter<PromiseHandle>
&&
is_extensible_promise_handle<PromiseHandle>;

// Detect is a type is an extensible awaitable.
template<
    typename PromiseHandle
> concept is_extensible_awaitable =
is_awaitable<PromiseHandle>
&&
is_extensible_promise_handle<PromiseHandle>;

// The void specialization exists to make all extensible_promise_handle
// classes support the is_extensible_promise_handle concept.
template<
> class extended_promise_handle<
    void
>
{
    template<
        typename Promise
    > friend class extensible_promise_handle;

    // This class can't be instantiated except by extensible_promise_handle.
    extended_promise_handle() {}
};

// An extensible awaitable is an object that can reference
// an extensible promise. They don't strictly need to be awaitable,
// but the intention is that most extensible_promise_handle objects
// will at some point be transformed into an awaitable object.
template<
    typename Promise
> class extensible_promise_handle
    :
    public extended_promise_handle<void>
{
    template<
        typename PromiseHandle
    > friend class extended_promise_handle;

public:
    using promise_type = Promise;
    using coroutine_handle_type = coroutine_handle<promise_type>;

private:
    coroutine_handle<promise_type> m_coroutineHandle;

public:
    explicit extensible_promise_handle(
        Promise& promise
    ) :
        m_coroutineHandle{ coroutine_handle_type::from_promise(promise) }
    {}

    explicit extensible_promise_handle(
        coroutine_handle_type coroutineHandle = nullptr
    ) :
        m_coroutineHandle { coroutineHandle }
    {}

protected:
    // Access the coroutine handle by reference.
    decltype(auto) handle()
    {
        return (m_coroutineHandle);
    }

    // Access the coroutine handle by reference.
    decltype(auto) handle() const
    {
        return (m_coroutineHandle);
    }

    // Access the promise by reference
    decltype(auto) promise() const
    {
        return m_coroutineHandle.promise();
    }

public:
    explicit operator bool() const noexcept
    {
        return handle().operator bool();
    }

    friend auto operator <=> (
        const extensible_promise_handle& left,
        const extensible_promise_handle& right
        ) noexcept
    {
        return left.handle() <=> right.handle();
    }

    friend auto operator == (
        const extensible_promise_handle& left,
        const extensible_promise_handle& right
        ) noexcept
    {
        return left.handle() == right.handle();
    }
};

template<
    typename PromiseHandle
> class extended_promise_handle
{
    // This assert should never fire, because we have specializations
    // for is_extensible_promise_handle and void, and that is the supported
    // set of types.
    static_assert(is_extensible_promise_handle<PromiseHandle>, "The PromiseHandle must be extensible_promise_handle.");
};

template<
    is_extensible_promise_handle PromiseHandle
> class extended_promise_handle<
    PromiseHandle
> :
    private value_storage<PromiseHandle>
{
    template<
        typename PromiseHandle
    > friend class extended_promise_handle;

public:
    using promise_type = typename std::decay_t<PromiseHandle>::promise_type;

protected:
    using promise_handle_type = PromiseHandle;

    using extended_promise_handle::value_storage::value_storage;

    decltype(auto) awaitable(
        this auto& self
    )
    {
        return self.extended_promise_handle::value();
    }

    decltype(auto) handle(
        this auto& self)
    {
        return self.extended_promise_handle::awaitable().handle();
    }

    decltype(auto) promise(
        this auto& self)
    {
        return self.extended_promise_handle::awaitable().promise();
    }

    friend auto operator <=> (
        const extended_promise_handle& left,
        const extended_promise_handle& right
        ) noexcept
    {
        return left.handle() <=> right.handle();
    }
};

template<
    typename PromiseHandle
> concept is_extended_promise_handle = is_derived_instantiation<PromiseHandle, extended_promise_handle>;

// This class helps for transferring ownership of single-owner awaitables.
template<
    typename Promise
> class single_owner_promise_handle
    :
    public extensible_promise_handle<Promise>
{
public:
    using typename single_owner_promise_handle::extensible_promise_handle::coroutine_handle_type;

    explicit single_owner_promise_handle(
        const single_owner_promise_handle&
    ) = delete;

    explicit single_owner_promise_handle(
        Promise& promise
    ) : extensible_promise_handle<Promise> { promise.handle() }
    {
    }

    explicit single_owner_promise_handle(
        coroutine_handle_type&& other = coroutine_handle_type{}
    )
    {
        std::swap(
            this->handle(),
            other
        );
    }

    single_owner_promise_handle(
        single_owner_promise_handle&& other
    )
    {
        std::swap(
            this->handle(),
            other.handle()
        );
    }

    auto& operator=(
        const single_owner_promise_handle& other
        ) = delete;

    auto& operator=(
        single_owner_promise_handle&& other
        )
    {
        auto temp = std::move(*this);

        std::swap(
            this->handle(),
            other.handle()
        );

        return *this;
    }

    void destroy()
    {
        if (this->handle())
        {
            this->handle().destroy();
            this->handle() = {};
        }
    }

    [[nodiscard]] auto destroy_on_scope_exit()
    {
        return scope_guard{ [&]() { this->destroy(); } };
    }

    ~single_owner_promise_handle()
    {
        destroy();
    }
};
}

using detail::extensible_promise;
using detail::is_extensible_promise;
using detail::extensible_promise_handle;
using detail::derived_promise;

}
