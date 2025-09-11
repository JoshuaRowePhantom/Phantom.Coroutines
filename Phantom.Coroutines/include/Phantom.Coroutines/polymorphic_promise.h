#ifndef PHANTOM_COROUTINES_INCLUDE_POLYMORPHIC_PROMISE_H
#define PHANTOM_COROUTINES_INCLUDE_POLYMORPHIC_PROMISE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <concepts>
#include <type_traits>
#include "Phantom.Coroutines/detail/config_macros.h"
#include "Phantom.Coroutines/detail/coroutine.h"
#include "Phantom.Coroutines/extensible_promise.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Bases
>
class polymorphic_promise
    :
    public Bases ...
{
public:
    using Bases::Bases...;

    virtual coroutine_handle<> handle() noexcept
    {
        return coroutine_handle<polymorphic_promise>::from_promise(*this);
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    detail::is_derived_instantiation<polymorphic_promise> Promise
>
class extensible_promise_handle<
    Promise
>
{
public:
    using promise_type = Promise;
    using coroutine_handle_type = coroutine_handle<>;

private:
    promise_type* m_promise = nullptr;

public:
    extensible_promise_handle() = default;

    explicit extensible_promise_handle(
        promise_type& promise
    ) :
        m_promise{ std::addressof(promise) }
    {
    }
    
protected:
    // Access the coroutine handle.
    coroutine_handle_type handle() const noexcept
    {
        return m_promise ? m_promise->handle() : coroutine_handle_type{};
    }

    // Access the promise by reference
    promise_type& promise() const
    {
        return *m_promise;
    }

    void destroy()
    {
        if (m_promise)
        {
            handle().destroy();
            m_promise = nullptr;
        }
    }

public:
    explicit operator bool() const noexcept
    {
        return m_promise;
    }

    friend auto operator <=> (
        const extensible_promise_handle& left,
        const extensible_promise_handle& right
        ) noexcept
    {
        return left.m_promise <=> right.m_promise;
    }

    friend bool operator == (
        const extensible_promise_handle& left,
        const extensible_promise_handle& right
        ) noexcept
    {
        return left.m_promise == right.m_promise;
    }
};

} // namespace Phantom::Coroutines

#endif