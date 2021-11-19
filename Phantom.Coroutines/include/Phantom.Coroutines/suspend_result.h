#include <type_traits>
#include "detail/coroutine.h"
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_awaiter Awaiter
>
class suspend_result_awaiter
{
    friend class suspend_result;

    suspend_result& m_suspendResult;
    Awaiter m_awaiter;

    template<
        is_awaiter CAwaiter
    > suspend_result_awaiter(
        suspend_result& suspendResult,
        Awaiter awaiter
    ) :
        m_suspendResult
    {
            suspendResult
    },
        m_awaiter
    {
            std::forward<CAwaiter>(awaiter)
    }
    {
    }

    template<
        has_co_await CAwaitable
    >
    suspend_result_awaiter(
        suspend_result& suspendResult,
        CAwaitable&& awaitable
    ) :
        m_suspendResult
    {
            suspendResult
    },
        m_awaiter
    {
            get_awaiter(std::forward<CAwaitable>(awaitable))
    }
    {
    }

public:
    bool await_ready(
    ) noexcept(noexcept(m_awaiter.await_ready()))
    {
        return m_awaiter.await_ready();
    }

    auto await_suspend(
        coroutine_handle<> continuation
    ) noexcept(noexcept(m_awaiter.await_suspend(continuation)))
    {
        if constexpr (has_void_await_suspend<Awaiter>)
        {
            m_awaiter.await_suspend(
                continuation
            );
            m_suspendResult.m_didSuspend = true;
            return;
        }
        else if constexpr (has_bool_await_suspend<Awaiter>)
        {
            return m_suspendResult.m_didSuspend = m_awaiter.await_suspend(
                continuation
            );
        }
        else
        {
            static_assert(has_symmetric_transfer_await_suspend<Awaiter>);

            auto transferToCoroutine = m_awaiter.await_suspend(
                continuation
            );

            m_suspendResult.m_didSuspend = transferToCoroutine != continuation;

            return transferToCoroutine;
        }
    }

    decltype(auto) await_resume(
    ) noexcept(noexcept(m_awaiter.await_resume()))
    {
        return (m_awaiter.await_resume());
    }
};

class suspend_result
{
    template<
        is_awaiter Awaiter
    > friend class suspend_result_awaiter;

    bool m_didSuspend = false;

public:
    bool did_suspend() const
    {
        return m_didSuspend;
    }

    template<
        is_awaiter Awaitable
    > auto operator <<(
        Awaitable&& awaitable
        )
    {
        return suspend_result_awaiter
        {
            *this,
            std::forward<Awaitable>(awaitable)
        };
    }

    template<
        has_co_await Awaitable
    > auto operator <<(
        Awaitable&& awaitable
        )
    {
        return suspend_result_awaiter<awaiter_type<Awaitable>>
        {
            *this,
            std::forward<Awaitable>(awaitable)
        };
    }
};


}

using detail::suspend_result;

}
