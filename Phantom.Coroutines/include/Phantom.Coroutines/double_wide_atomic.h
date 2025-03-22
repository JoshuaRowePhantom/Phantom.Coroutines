#ifndef PHANTOM_COROUTINES_INCLUDE_DOUBLE_WIDE_ATOMIC_H
#define PHANTOM_COROUTINES_INCLUDE_DOUBLE_WIDE_ATOMIC_H

#include <algorithm>
#include <atomic>
#include <concepts>
#include <type_traits>

namespace Phantom::Coroutines
{

#if _MSC_VER && _M_AMD64

namespace detail
{
template<
    typename T
> concept is_double_wide_value =
std::is_trivially_copy_assignable_v<T>
&& sizeof(T) <= 16;
}

template<
    detail::is_double_wide_value Value
>
struct double_wide_value
{
    alignas(std::max(alignof(Value), size_t(16)))
    Value m_value;

    operator Value() const { return m_value; }
    auto operator->(this auto&& self) { return &self.m_value; }
    double_wide_value& operator=(Value&& value)
    {
        m_value = std::move(value);
        return *this;
    }
    double_wide_value& operator=(const Value& value)
    {
        m_value = value;
        return *this;
    }
};

}

namespace std
{
template<
    typename T
> struct atomic<::Phantom::Coroutines::double_wide_value<T>>
{
public:
    using value_type = ::Phantom::Coroutines::double_wide_value<T>;
    mutable value_type m_value;

    using atomic_ref_type = std::atomic_ref<value_type>;

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
        atomic_ref_type ref(m_value);
        return ref.compare_exchange_weak(
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
        atomic_ref_type ref(m_value);
        return ref.compare_exchange_strong(
            expected,
            desired);
    }

    value_type exchange(
        value_type desired,
        std::memory_order = std::memory_order_seq_cst
    ) noexcept
    {
        atomic_ref_type ref(m_value);
        return ref.exchange(
            desired);
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
        std::memory_order order = std::memory_order_seq_cst
    ) const noexcept
    {
        atomic_ref_type ref(m_value);
        return ref.load(order);
    }

    void store(
        value_type value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        atomic_ref_type ref(m_value);
        return ref.store(
            value,
            order);

    }
};

#endif

}

#endif
