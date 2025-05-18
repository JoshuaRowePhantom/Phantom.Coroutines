#ifndef PHANTOM_COROUTINES_INCLUDE_ATOMIC_SHARED_PTR_H
#define PHANTOM_COROUTINES_INCLUDE_ATOMIC_SHARED_PTR_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#if __cpp_lib_atomic_shared_ptr
#include <memory>
#else
#include <atomic>
#include <concepts>
#include <mutex>
#endif
#include "config_macros.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::detail
{

#if __cpp_lib_atomic_shared_ptr
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> using atomic_shared_ptr = std::atomic<std::shared_ptr<T>>;
#else
template<
    typename T
>
class atomic_mutex_impl
{
    atomic_mutex_impl(const atomic_mutex_impl&) = delete;
    atomic_mutex_impl(atomic_mutex_impl&&) = delete;
    atomic_mutex_impl& operator=(const atomic_mutex_impl&) = delete;
    atomic_mutex_impl& operator=(atomic_mutex_impl&&) = delete;

    mutable std::mutex m_mutex;
    T m_value;

public:
    template<
        typename... Args
    >
    requires std::constructible_from<T, Args...>
    atomic_mutex_impl(
        Args&& ... args
    ) :
        m_value{ std::forward<Args>(args)... }
    { }

    T load(
        std::memory_order = std::memory_order_seq_cst
    ) const
    { 
        std::unique_lock lock{ m_mutex };
        return m_value;
    }

    void store(
        T value,
        std::memory_order = std::memory_order_seq_cst
    )
    { 
        std::unique_lock lock{ m_mutex };
        m_value = value;
    }
    
    T exchange(
        T value,
        std::memory_order = std::memory_order_seq_cst
    )
    {
        std::unique_lock lock{ m_mutex };
        using std::swap;
        swap(m_value, value);
        return std::move(value);
    }

    bool compare_exchange_strong(
        T& expected,
        T desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    )
    { 
        using std::swap;
        std::unique_lock lock{ m_mutex };
        if (m_value == expected)
        {
            swap(expected, m_value);
            swap(m_value, desired);
            return true;
        }
        return false;
    }

    bool compare_exchange_weak(
        T& expected,
        T desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    )
    { 
        return compare_exchange_strong(expected, desired);
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> 
class atomic_shared_ptr :
    public atomic_mutex_impl<std::shared_ptr<T>>
{
    using atomic_shared_ptr::atomic_mutex_impl::atomic_mutex_impl;
};
#endif

}

#endif
