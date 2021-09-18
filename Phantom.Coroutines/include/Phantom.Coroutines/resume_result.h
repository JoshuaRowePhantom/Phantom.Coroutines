#include <type_traits>
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{

template<
    typename TAwaiter
>
class always_suspended_resume_result
{
    TAwaiter m_awaiter;
public:
    always_suspended_resume_result(
        TAwaiter&& awaiter
    ) : m_awaiter{
        awaiter
    }
    {}

    bool did_suspend() const { return true; }

    auto result() noeexcept(noexcept(m_awaiter.await_resume()))
    {
        return (m_awaiter.await_resume());
    }
};

template<
    typename TAwaiter
>
class maybe_suspended_resume_result
{
    TAwaiter m_awaiter;
    bool m_suspended;

public:
    maybe_suspended_resume_result(
        TAwaiter&& awaiter,
        bool suspended
    ) :
        m_awaiter{
        awaiter
    },
        m_suspended{
            suspended
    }
    {}

    bool did_suspend() const { return m_suspended; }

    auto result() noeexcept(noexcept(m_awaiter.await_resume()))
    {
        return (m_awaiter.await_resume());
    }
};

template <
    typename TAwaiter,
    typename TAwait_suspend_result = decltype(std::declval<TAwaiter>().await_suspend(std::declval<coroutine_handle<>>()))
>
class resume_result_awaiter
{
    static_assert(std::is_same_v<void, TAwait_suspend_result>);
    TAwaiter m_awaiter;

public:
    resume_result_awaiter(
        TAwaiter&& awaiter
    ) : m_awaiter(
        awaiter
    )
    {}

    auto await_ready() noexcept
    {
        return m_awaiter.await_ready();
    }

    template<
        typename TPromise
    >
    void await_suspend(
        coroutine_handle<TPromise> coroutine
    ) noexcept
    {
        return m_awaiter.await_suspend(
            coroutine
        );
    }

    auto await_resume() noexcept
    {
        return always_suspended_resume_result{ std::move(m_awaiter) };
    }
};

template <
    typename TAwaiter
>
class resume_result_awaiter<
    TAwaiter,
    bool
>
{
    TAwaiter m_awaiter;
    bool m_suspended;

public:
    resume_result_awaiter(
        TAwaiter&& awaiter
    ) : m_awaiter(
        awaiter
    )
    {}

    auto await_ready() noexcept
    {
        return m_awaiter.await_ready();
    }

    template<
        typename TPromise
    >
    bool await_suspend(
        coroutine_handle<TPromise> coroutine
    )
    {
        m_suspended = m_awaiter.await_suspend(
            coroutine);
        return m_suspended;
    }

    auto await_resume() noexcept
    {
        return maybe_suspended_resume_result{ std::move(m_awaiter), m_suspended };
    }
};

template <
    typename TAwaiter
>
class resume_result_awaiter<
    TAwaiter,
    coroutine_handle<>
>
{
    TAwaiter m_awaiter;
    bool m_suspended;

public:
    resume_result_awaiter(
        TAwaiter&& awaiter
    ) : m_awaiter(
        awaiter
    )
    {}

    auto await_ready() noexcept
    {
        return m_awaiter.await_ready();
    }

    template<
        typename TPromise
    >
    auto await_suspend(
        coroutine_handle<TPromise> coroutine
    )
    {
        auto await_suspend_result = m_awaiter.await_suspend(
            coroutine);

        m_suspended = await_suspend_result != coroutine;

        return await_suspend_result;
    }

    auto await_resume() noexcept
    {
        return maybe_suspended_resume_result{ std::move(m_awaiter), m_suspended };
    }
};

template<
    typename TAwaiter
> auto with_resume_result(
    TAwaitable&& awaitable
)
{
    return resume_result_awaiter(
        operator co_await(awaitable)
    );
}

}