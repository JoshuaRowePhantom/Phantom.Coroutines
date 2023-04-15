#pragma once
#include <atomic>
#include <concepts>
#include "detail/immovable_object.h"
#include "type_traits.h"
#include "double_wide_atomic.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename Value,
    is_continuation Continuation
> class basic_async_atomic
    :
private immovable_object
{
    class awaiter;

    struct atomic_value
    {
        Value m_value;
        awaiter* m_awaiters;
    };
    using double_wide_atomic_value = double_wide_value<atomic_value>;
    std::atomic<double_wide_atomic_value> m_doubleWideAtomic;

    void signal_awaiters(
        Value newValue)
    {
    }

    auto signal_awaiters_on_scope_exit(
        Value newValue)
    {
        return scope_exit([&, newValue] { signal_awaiters(newValue); });
    }

    class awaiter
    {
        friend class basic_async_atomic<Value, Continuation>;

        basic_async_atomic* m_atomic;
        std::memory_order m_order;
        Value m_value;
        Continuation m_continuation;
        awaiter* m_nextAwaiter;

    public:

        awaiter(
            basic_async_atomic* atomic,
            Value value,
            std::memory_order order
        ) :
            m_atomic(atomic),
            m_value(value),
            m_order(order)
        {
        }

        bool await_ready(
        ) const noexcept
        {
            return false;
        }

        bool await_suspend(
            Continuation continuation
        ) noexcept
        {
            m_continuation = continuation;
            
            double_wide_atomic_value expected = m_atomic->m_doubleWideAtomic.load_inconsistent(
                m_order
            );
            double_wide_atomic_value desired;
            desired->m_value = expected->m_value;

            do
            {
                if (expected->m_value != m_value)
                {
                    // The value has changed, so we don't need to await.
                    m_value = expected->m_value;
                    return false;
                }

                m_nextAwaiter = expected->m_awaiters;
                desired->m_awaiters = this;
            }
            while (!m_atomic->m_doubleWideAtomic.compare_exchange_weak(
                expected,
                desired,
                std::memory_order_acq_rel
            ));

            return true;
        }

        Value await_resume(
        ) const noexcept
        {
            return m_value;
        }
    };

public:
    using value_type = Value;

    explicit basic_async_atomic(
        Value value = Value{}
    ) :
        m_doubleWideAtomic({ value, nullptr })
    {
    }

    auto wait(
        Value value,
        std::memory_order order = std::memory_order_seq_cst
    ) const noexcept
    {
        return awaiter
        {
            const_cast<basic_async_atomic*>(this),
            value,
            order
        };
    }

    auto load(
        std::memory_order order = std::memory_order_seq_cst
    ) const noexcept
    {
        return m_doubleWideAtomic.load_inconsistent(order)->m_value;
    }

    void store(
        Value value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        exchange(value);
    }
    
    auto exchange(
        Value desired,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        Value expected = m_doubleWideAtomic.load_inconsistent(std::memory_order_relaxed)->m_value;
        while (!compare_exchange_weak(
            expected,
            desired
        ));
        return expected;
    }

    bool compare_exchange_weak(
        Value& expected,
        Value desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        // Do this to load the current m_awaiters value.
        double_wide_atomic_value expectedDoubleWide = m_doubleWideAtomic.load_inconsistent();
        expectedDoubleWide->m_value = expected;

        double_wide_atomic_value desiredDoubleWide;
        desiredDoubleWide->m_value = desired;
        desiredDoubleWide->m_awaiters = expectedDoubleWide->m_awaiters;
        if (expectedDoubleWide->m_value != desired)
        {
            desiredDoubleWide->m_awaiters = nullptr;
        }
        
        if (!m_doubleWideAtomic.compare_exchange_strong(
            expectedDoubleWide,
            desiredDoubleWide
        ))
        {
            expected = expectedDoubleWide->m_value;
            return false;
        }

        if (expected == desired)
        {
            return true;
        }

        awaiter* nextAwaiter;

        for (auto awaiter = expectedDoubleWide->m_awaiters;
            awaiter;
            awaiter = nextAwaiter)
        {
            nextAwaiter = awaiter->m_nextAwaiter;
            awaiter->m_value = desired;
            awaiter->m_continuation.resume();
        }

        return true;
    }

    bool compare_exchange_strong(
        Value& expected,
        Value desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    )
    {
        Value weakExpected = expected;
        bool result;
        while (
            !(result = compare_exchange_weak(
                weakExpected,
                desired
            ))
            &&
            weakExpected == expected);

        expected = weakExpected;
        return result;
    }
};

template<
    typename Value
> using async_atomic = basic_async_atomic<
    Value,
    std::coroutine_handle<>
>;

}

using detail::basic_async_atomic;
using detail::async_atomic;

}
