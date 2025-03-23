#ifndef PHANTOM_COROUTINES_INCLUDE_AWAITER_WRAPPER_H
#define PHANTOM_COROUTINES_INCLUDE_AWAITER_WRAPPER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <optional>
#include "detail/config.h"
#include "extensible_promise.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename Value
> class awaiter_wrapper_storage
    :
    private value_storage<Value>
{
    template<
        is_awaitable Awaitable
    > friend class awaiter_wrapper;

    using awaiter_wrapper_storage::value_storage::value_storage;

public:
    decltype(auto) awaitable(
        this auto& self
    )
    {
        return self.awaiter_wrapper_storage::value_storage::value();
    }
};

template<
    is_extensible_promise_handle Object
> class awaiter_wrapper_storage<
    Object
> :
    public extended_promise_handle<Object>
{
    template<
        is_awaitable Awaitable
    > friend class awaiter_wrapper;

public:
    using awaiter_wrapper_storage::extended_promise_handle::extended_promise_handle;
};

template<
    is_awaiter Awaiter,
    typename Scope
> class awaiter_wrapper_methods
{
public:
    // Default implementations of await_ready,
    // await_suspend, and await_resume that forward
    // all arguments.
    decltype(auto) await_ready(
        this auto&& self,
        auto&&... args)
        noexcept(noexcept(
            std::forward<decltype(self)>(self).Scope::awaiter().await_ready(
                std::forward<decltype(args)>(args)...)))
        
    {
        return std::forward<decltype(self)>(self).Scope::awaiter().await_ready(
            std::forward<decltype(args)>(args)...);
    }

    decltype(auto) await_suspend(
        this auto&& self,
        auto&&... args)
        noexcept(noexcept(
            std::forward<decltype(self)>(self).Scope::awaiter().await_suspend(
                std::forward<decltype(args)>(args)...)))
    {
        return std::forward<decltype(self)>(self).Scope::awaiter().await_suspend(
            std::forward<decltype(args)>(args)...);
    }

    decltype(auto) await_resume(
        this auto&& self,
        auto&&... args)
        noexcept(noexcept(
            std::forward<decltype(self)>(self).Scope::awaiter().await_resume(
                std::forward<decltype(args)>(args)...)))
    {
        return std::forward<decltype(self)>(self).Scope::awaiter().await_resume(
            std::forward<decltype(args)>(args)...);
    }
};

template<
    is_awaitable Awaitable
> class awaiter_wrapper;

// The is_awaiter specialization provides the behavior of wrapping
// an actual awaiter object.
template<
    is_awaiter Awaiter
> class awaiter_wrapper<
    Awaiter
> :
    public awaiter_wrapper_storage<Awaiter>,
    public awaiter_wrapper_methods<Awaiter, awaiter_wrapper<Awaiter>>
{
    friend class awaiter_wrapper_methods<Awaiter, awaiter_wrapper<Awaiter>>;

protected:
    typedef Awaiter awaiter_type;

    using awaiter_wrapper::awaiter_wrapper_storage::awaiter_wrapper_storage;

protected:
    awaiter_type& awaiter() noexcept
    {
        return this->awaitable();
    }
};

template<
    is_awaitable Awaitable
> class awaiter_wrapper
    :
    // Note that awaiter_wrapper_awaitable_storage is first so that it is
    // constructed before awaiter_wrapper and destroyed after awaiter_wrapper.
    public awaiter_wrapper_storage<Awaitable>,
    public awaiter_wrapper_methods<awaiter_type<Awaitable>, awaiter_wrapper<Awaitable>>
{
    template<
        is_awaitable
    > friend class awaiter_wrapper;

    template<
        is_awaiter Awaiter,
        typename Scope
    > friend class awaiter_wrapper_methods;

    template<
        typename PromiseHandle
    > friend class extended_promise_handle;

public:
    using awaitable_type = Awaitable;
    using awaiter_type = awaiter_type<Awaitable>;

private:
    using awaiter_storage = awaiter_wrapper_storage<awaiter_type>;
    std::optional<awaiter_storage> m_awaiter;

    auto get_awaiter_lambda()
    {
        return [&]() -> decltype(auto) 
        { 
            return get_awaiter(std::forward<Awaitable>(this->awaitable()));
        };
    }

    decltype(auto) retrieve_from_extended_promise_handle(
        this auto& self,
        auto awaiterRetriever,
        auto awaitableRetriever
    )
    {
        if constexpr (
            is_extended_promise_handle<awaitable_type>
            && is_extended_promise_handle<awaiter_type>
            )
        {
            if (self.awaiter_wrapper::m_awaiter)
            {
                return awaiterRetriever(*self.awaiter_wrapper::m_awaiter);
            }
            else
            {
                return awaitableRetriever(self);
            }
        }
        else if constexpr (is_extended_promise_handle<awaiter_type>)
        {
            std::ignore = self.awaiter();
            return awaiterRetriever(*self.awaiter_wrapper::m_awaiter);
        }
        else
        {
            return awaitableRetriever(self);
        }
    }

public:
    awaiter_wrapper()
    {
    }

    explicit awaiter_wrapper(
        std::invocable auto&& awaitableFunction
    )
        : 
        awaiter_wrapper_storage<Awaitable>
    {
        std::forward<decltype(awaitableFunction)>(awaitableFunction)
    }
    {}

public:
    decltype(auto) awaiter(
        this auto& self)
    {
        if (!self.awaiter_wrapper::m_awaiter)
        {
            self.awaiter_wrapper::m_awaiter.emplace(
                self.awaiter_wrapper::get_awaiter_lambda());
        }
        return self.awaiter_wrapper::m_awaiter->awaitable();
    }

    decltype(auto) handle(
        this auto& self
    )
    {
        return self.awaiter_wrapper::retrieve_from_extended_promise_handle(
            [](auto&& awaiter) -> decltype(auto) { return awaiter.handle(); },
            [](auto& self) -> decltype(auto) { return self.awaiter_wrapper::template awaiter_wrapper_storage<Awaitable>::handle(); }
        );
    }

    decltype(auto) promise(
        this auto& self
    )
    {
        return self.awaiter_wrapper::retrieve_from_extended_promise_handle(
            [](auto&& awaiter) -> decltype(auto) { return awaiter.promise(); },
            [](auto& self) -> decltype(auto) { return self.awaiter_wrapper::template awaiter_wrapper_storage<Awaitable>::promise(); }
        );
    }
};

}
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::awaiter_wrapper;
}
#endif
