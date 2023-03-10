#pragma once

#include "policies.h"
#include <future>
#include <mutex>
#include <concepts>
#include "detail/atomic_state.h"

namespace Phantom::Coroutines
{

template<
    is_awaiter_cardinality_policy ConsumerPolicy,
    typename DerivedAwaiter
> class awaiter_list_entry;

template<
    is_await_cancellation_policy WaitCancellationPolicy,
    typename Awaiter,
    detail::is_atomic_state_type State
> class awaiter_list;

template<
    typename DerivedAwaiter
> class awaiter_list_entry<
    single_awaiter,
    DerivedAwaiter
>
{
public:
    void set_next(
        DerivedAwaiter* next
    )
    {
        assert(next == nullptr);
    }

    DerivedAwaiter* next() const
    {
        return nullptr;
    }
};

template<
    typename DerivedAwaiter
> class awaiter_list_entry<
    multiple_awaiters,
    DerivedAwaiter
>
{
    DerivedAwaiter* m_next = nullptr;

public:
    void set_next(
        DerivedAwaiter* next
    )
    {
        m_next = next;
    }

    DerivedAwaiter* next() const
    {
        return m_next;
    }
};

template<
    typename Awaiter
> concept is_awaiter_list_entry = requires(
    Awaiter * awaiter
)
{
    { awaiter->set_next(awaiter) };
    { awaiter->next() } -> std::same_as<Awaiter*>;
};

template<
    is_await_cancellation_policy AwaitCancellationPolicy
> class awaiter_list_mutex;

template<
> class awaiter_list_mutex<
    await_is_cancellable
>
{
    std::mutex m_mutex;

protected:
    typedef std::scoped_lock<std::mutex> lock_type;

    lock_type acquire_mutex()
    {
        return lock_type{ m_mutex };
    }
};

template<
> class awaiter_list_mutex<
    await_is_not_cancellable
>
{
protected:
    struct lock_type
    {
        void unlock() noexcept
        {
        }
    };

    auto acquire_mutex() noexcept
    {
        return lock_type{};
    }
};

template<
    is_awaiter_list_entry Awaiter
> void invoke_on_awaiters(
    Awaiter* awaiters,
    std::invocable<Awaiter*> auto&& invocation
)
{
    while (awaiters)
    {
        auto nextAwaiter = awaiters->next();
        invocation(awaiters);
        awaiters = nextAwaiter;
    }
}

// Given a source list of awaiters, reverse it
// and prepend it to the destination list.
template<
    is_awaiter_list_entry Awaiter
> void reverse_and_prepend_awaiter_list(
    Awaiter* source,
    Awaiter** destination
)
{
    invoke_on_awaiters(
        source,
        [&](auto awaiter)
    {
        awaiter->set_next(*destination);
        *destination = awaiter;
    });
}

inline void resume_from_destruction_of_awaitable_object(
    noop_on_destroy
) noexcept
{}

inline void resume_from_destruction_of_awaitable_object(
    throw_on_destroy
) 
{
    throw std::future_error(
        std::future_errc::broken_promise
    );
}

inline void resume_from_destruction_of_awaitable_object(
    fail_on_destroy_with_awaiters
)
{
    assert(false);
}
}
