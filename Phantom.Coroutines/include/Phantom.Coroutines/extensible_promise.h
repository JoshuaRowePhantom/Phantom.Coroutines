#ifndef PHANTOM_COROUTINES_INCLUDE_EXTENSIBLE_PROMISE_H
#define PHANTOM_COROUTINES_INCLUDE_EXTENSIBLE_PROMISE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <tuple>
#include <type_traits>
#include "Phantom.Coroutines/detail/coroutine.h"
#include "Phantom.Coroutines/detail/scope_guard.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

// An extensible_promise is a promise type that can
// be extended or wrapped by other promise types.
PHANTOM_COROUTINES_MODULE_EXPORT
class extensible_promise
{
    // promise objects are not meant to be copied or moved
    extensible_promise(
        const extensible_promise&
    ) = delete;
public:
    extensible_promise() = default;

    auto handle(
        this auto& self
    ) noexcept
    {
        return coroutine_handle<
            std::remove_cvref_t<decltype(self)>
        >::from_promise(self);
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
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

namespace detail
{
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
    PHANTOM_COROUTINES_MSVC_INSTRINSIC
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
    ) requires (
        !std::constructible_from<Base, Args&&...>
        && std::constructible_from<Base>)
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

} // namespace detail

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_extensible_promise BasePromise,
    typename ... Bases
>
class derived_promise :
    public detail::derived_promise_impl<
    BasePromise,
    std::tuple<Bases...>,
    typename detail::filter_types
    <
        detail::has_await_transform_filter,
        detail::derived_promise_await_transform<BasePromise, Bases...>,
        detail::derived_promise_base<Bases>...
    >::tuple_type
>
{
    using derived_promise::derived_promise_impl::derived_promise_impl;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class extensible_promise_handle;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename PromiseHandle
> class extended_promise_handle;

// Detect is a type is an extensible awaitable.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename PromiseHandle
> concept is_extensible_promise_handle = 
detail::is_derived_instantiation<
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
PHANTOM_COROUTINES_MODULE_EXPORT
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
    coroutine_handle_type& handle()
    {
        return m_coroutineHandle;
    }

    // Access the coroutine handle by reference.
    const coroutine_handle_type& handle() const
    {
        return m_coroutineHandle;
    }

    // Access the promise by reference
    Promise& promise() const
    {
        return m_coroutineHandle.promise();
    }

    void destroy()
    {
        if (handle())
        {
            handle().destroy();
            handle() = coroutine_handle_type{};
        }
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

    friend bool operator == (
        const extensible_promise_handle& left,
        const extensible_promise_handle& right
        ) noexcept
    {
        return left.handle() == right.handle();
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
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
    private detail::value_storage<PromiseHandle>
{
    template<
        typename
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
        return self.template extended_promise_handle<PromiseHandle>::value();
    }

    decltype(auto) handle(
        this auto& self)
    {
        return self.template extended_promise_handle<PromiseHandle>::awaitable().handle();
    }

    decltype(auto) promise(
        this auto& self)
    {
        return self.template extended_promise_handle<PromiseHandle>::awaitable().promise();
    }

    friend auto operator <=> (
        const extended_promise_handle& left,
        const extended_promise_handle& right
        ) noexcept
    {
        return left.handle() <=> right.handle();
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename PromiseHandle
> concept is_extended_promise_handle = detail::is_derived_instantiation<PromiseHandle, extended_promise_handle>;

// This class helps for transferring ownership of single-owner awaitables.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class single_owner_promise_handle
    :
    public extensible_promise_handle<Promise>
{
protected:
    using single_owner_promise_handle::extensible_promise_handle::destroy;

public:
    using typename single_owner_promise_handle::extensible_promise_handle::coroutine_handle_type;

    single_owner_promise_handle(
        const single_owner_promise_handle&
    ) = delete;

    single_owner_promise_handle(
        Promise& promise
    ) : extensible_promise_handle<Promise> { promise }
    {
    }

    template<
        typename Other
    >
        requires std::constructible_from<extensible_promise_handle<Promise>, Other&>
    single_owner_promise_handle(
        std::reference_wrapper<Other> promise
    ) : extensible_promise_handle<Promise> { static_cast<Other&>(promise) }
    {
    }

    single_owner_promise_handle(
        coroutine_handle_type other = coroutine_handle_type{}
    ) : extensible_promise_handle<Promise> { other }
    {
    }

    single_owner_promise_handle(
        single_owner_promise_handle&& other
    )
    {
        using std::swap;
        swap<extensible_promise_handle<Promise>>(
            *this,
            other
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

        using std::swap;
        swap(
            this->handle(),
            other.handle()
        );

        return *this;
    }

    [[nodiscard]] auto destroy_on_scope_exit()
    {
        return detail::scope_guard{ [&]() { this->destroy(); } };
    }

    ~single_owner_promise_handle()
    {
        destroy();
    }
};

}

#endif
