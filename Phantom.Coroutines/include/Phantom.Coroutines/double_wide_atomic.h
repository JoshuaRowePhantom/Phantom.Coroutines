#pragma once

#include <atomic>
#include <intrin.h>
#include <type_traits>
#include <concepts>

namespace Phantom::Coroutines
{

#if _MSC_VER && _M_AMD64

namespace detail
{
template<
    typename T
> concept is_double_wide_value =
std::is_trivially_copy_assignable_v<T>
&& sizeof(T) <= 16
&& alignof(T) <= 16;
}

template<
    detail::is_double_wide_value Value
>
class alignas(16) double_wide_value
{
    friend struct ::std::atomic<::Phantom::Coroutines::double_wide_value<Value>>;

    union
    {
        Value m_value;
        __int64 rawValue[2];
    };

public:
    double_wide_value(
        Value value = {})
        : m_value { value }
    {}

    operator Value() const { return m_value; }
    auto operator->(this auto&& self) { return &self.m_value; }
};

}

namespace std
{
template<
    ::Phantom::Coroutines::detail::is_double_wide_value T
> struct atomic<::Phantom::Coroutines::double_wide_value<T>>
{
public:
    using value_type = ::Phantom::Coroutines::double_wide_value<T>;
    value_type m_value;

public:
    atomic(
        T value = { }
    ) noexcept
        : m_value{ value }
    {}

    bool compare_exchange_weak(
        value_type& expected,
        value_type desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        return compare_exchange_strong(
            expected,
            desired);
    }

    bool compare_exchange_strong(
        value_type& expected,
        value_type desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        return ::_InterlockedCompareExchange128(
            m_value.rawValue,
            desired.rawValue[1],
            desired.rawValue[0],
            expected.rawValue);
    }

    value_type exchange(
        value_type desired,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        auto expected = load_inconsistent();
        while (!compare_exchange_weak(
            expected,
            desired
        ));
        return expected;
    }

    value_type load_inconsistent(
        std::memory_order order = std::memory_order_seq_cst
    ) const noexcept
    {
        auto result = m_value;
        if (order < std::memory_order_acq_rel)
        {
            order = std::memory_order_acq_rel;
        }
        std::atomic_thread_fence(
            order);
        return result;
    }

    value_type load(
        std::memory_order = std::memory_order_seq_cst
    ) const noexcept
    {
        auto value = load_inconsistent();
        while (!const_cast<atomic*>(this)->compare_exchange_weak(
            value,
            value
        ));
        return value;
    }

    void store(
        value_type value,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        exchange(value);
    }
};

#endif

}

