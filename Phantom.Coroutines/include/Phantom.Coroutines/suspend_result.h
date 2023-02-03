#pragma once

#include <type_traits>
#include "awaiter_wrapper.h"
#include "detail/coroutine.h"
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_awaitable Awaitable
>
class suspend_result_awaiter
    :
public awaiter_wrapper<Awaitable>
{
    friend class suspend_result;
    using typename awaiter_wrapper<Awaitable>::awaiter_type;

    suspend_result& m_suspendResult;
    
    suspend_result_awaiter(
        suspend_result& suspendResult,
        Awaitable&& awaitable
    ) :
    awaiter_wrapper<Awaitable> 
    {
        [&]() -> decltype(auto) { return std::forward<Awaitable>(awaitable); }
    },
     m_suspendResult
    {
        suspendResult
    }
    {
    }

public:
    bool await_ready(
    ) noexcept(noexcept(this->awaiter().await_ready()))
    {
        return this->awaiter().await_ready();
    }

    template<
        is_coroutine_handle Continuation
    > auto await_suspend(
        Continuation continuation
    ) noexcept(noexcept(this->awaiter().await_suspend(continuation)))
    {
        if constexpr (has_void_await_suspend<awaiter_type, Continuation>)
        {
            m_suspendResult.m_didSuspend = true;
            this->awaiter().await_suspend(
                continuation
            );
            return;
        }
        else if constexpr (has_bool_await_suspend<awaiter_type, Continuation>)
        {
            return m_suspendResult.m_didSuspend = this->awaiter().await_suspend(
                continuation
            );
        }
        else
        {
            static_assert(has_symmetric_transfer_await_suspend<awaiter_type, Continuation>);

            auto transferToCoroutine = this->awaiter().await_suspend(
                continuation
            );

            m_suspendResult.m_didSuspend = transferToCoroutine != continuation;

            return transferToCoroutine;
        }
    }

    decltype(auto) await_resume(
    ) noexcept(noexcept(this->awaiter().await_resume()))
    {
        return (this->awaiter().await_resume());
    }
};

class suspend_result
{
    template<
        is_awaitable Awaitable
    > friend class suspend_result_awaiter;

    bool m_didSuspend = false;

public:
    bool did_suspend() const
    {
        return m_didSuspend;
    }

    template<
        is_awaitable Awaitable
    > auto operator <<(
        Awaitable&& awaitable
        )
    {
        return suspend_result_awaiter<
            Awaitable&&
        >(
            *this,
            std::forward<Awaitable>(awaitable)
            );
    }
};


}

using detail::suspend_result;

}
