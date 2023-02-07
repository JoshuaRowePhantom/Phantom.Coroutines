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
    friend class ::std::atomic<::Phantom::Coroutines::double_wide_value<Value>>;

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
    auto operator->(this auto& self) { return &self.m_value; }
};

}

namespace std
{
template<
    ::Phantom::Coroutines::detail::is_double_wide_value T
> class atomic<::Phantom::Coroutines::double_wide_value<T>>
{
public:
    using value_type = ::Phantom::Coroutines::double_wide_value<T>;
    value_type m_value;

public:
    atomic(T value = { })
        : m_value{ value }
    {}

    bool compare_exchange_weak(
        value_type& expected,
        value_type desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst)
    {
        return compare_exchange_strong(
            expected,
            desired);
    }

    bool compare_exchange_strong(
        value_type& expected,
        value_type desired,
        std::memory_order = std::memory_order_seq_cst,
        std::memory_order = std::memory_order_seq_cst)
    {
        return ::_InterlockedCompareExchange128(
            m_value.rawValue,
            desired.rawValue[1],
            desired.rawValue[0],
            expected.rawValue);
    }

    value_type load_inconsistent(
    ) const
    {
        return m_value;
    }

    value_type load(
        std::memory_order memoryOrder = std::memory_order_seq_cst
    ) const
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
        std::memory_order = std::memory_order_seq_cst)
    {
        auto oldValue = load_inconsistent();
        while (!compare_exchange_weak(
            oldValue,
            value
        ));
    }
};

#endif

}

