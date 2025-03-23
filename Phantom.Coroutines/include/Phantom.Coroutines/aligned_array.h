#ifndef PHANTOM_COROUTINES_INCLUDE_ALIGNED_ARRAY_H
#define PHANTOM_COROUTINES_INCLUDE_ALIGNED_ARRAY_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/config.h"
#include<array>
#include<cstddef>
#include<compare>
#include<new>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    size_t Size,
    size_t Alignment
>
struct aligned_array
{
    using value_type = T;
    using size_type = size_t;
    using difference_type = ptrdiff_t;
    using reference = T&;
    using const_reference = const T&;
    using pointer = T*;
    using const_pointer = const T*;

    static constexpr size_t alignment = Alignment;

    // This is public to support aggregate initialization.
    // Do not use directly.
    // Disable warning that structure padded due to alignment specifier
    __pragma(warning(suppress:4324))
    struct alignas(Alignment) aligned_value
    {
        T _value;

        friend bool operator==(const aligned_value&, const aligned_value&) = default;
        friend auto operator<=>(const aligned_value&, const aligned_value&) = default;
    };

private:
    using array_type = std::array<aligned_value, Size>;
public:
    // This is public to support aggregate initialization.
    // Do not use directly.
    array_type _values;

    template<
        typename ArrayIterator
    >
    class basic_iterator
    {
        ArrayIterator m_iterator;

    public:
        constexpr basic_iterator(
            ArrayIterator iterator = {}
        ) : m_iterator{ iterator }
        {
        }

        friend bool operator==(const basic_iterator&, const basic_iterator&) = default;
        friend auto operator<=>(const basic_iterator&, const basic_iterator&) = default;

        auto& operator*() const
        {
            return m_iterator->_value;
        }

        auto operator->() const
        {
            return &m_iterator->_value;
        }

        auto& operator++()
        {
            m_iterator++;
            return *this;
        }

        auto& operator--()
        {
            m_iterator--;
            return *this;
        }
        
        auto operator++(int)
        {
            auto result = *this;
            m_iterator++;
            return result;
        }

        auto operator--(int)
        {
            auto result = *this;
            m_iterator--;
            return result;
        }

        auto& operator+=(difference_type difference)
        {
            m_iterator += difference;
            return *this;
        }

        auto& operator-=(difference_type difference)
        {
            m_iterator -= difference;
            return *this;
        }

        auto operator+(difference_type difference) const
        {
            return basic_iterator{ m_iterator + difference };
        }

        auto operator-(difference_type difference) const
        {
            return basic_iterator{ m_iterator - difference };
        }

        auto& operator[](difference_type difference) const
        {
            return m_iterator[difference]._value;
        }
    };

    constexpr auto begin(this auto& self) noexcept
    {
        return basic_iterator{ self._values.begin() };
    }

    constexpr auto cbegin(this const auto& self) noexcept
    {
        return basic_iterator{ self._values.cbegin() };
    }

    constexpr auto end(this auto& self) noexcept
    {
        return basic_iterator{ self._values.end() };
    }

    constexpr auto cend(this const auto& self) noexcept
    {
        return basic_iterator{ self._values.cend() };
    }

    constexpr auto rbegin(this auto& self) noexcept
    {
        return basic_iterator{ self._values.rbegin() };
    }

    constexpr auto crbegin(this const auto& self) noexcept
    {
        return basic_iterator{ self._values.crbegin() };
    }

    constexpr auto rend(this auto& self) noexcept
    {
        return basic_iterator{ self._values.rend() };
    }

    constexpr auto crend(this const auto& self) noexcept
    {
        return basic_iterator{ self._values.crend() };
    }

    constexpr auto& at(this auto& self, size_type position)
    {
        return self._values.at(position)._value;
    }

    constexpr auto& operator[](this auto& self, size_type position) noexcept
    {
        return self._values[position]._value;
    }

    constexpr auto& front(this auto& self) noexcept
    {
        return self._values.front()._value;
    }

    constexpr auto& back(this auto& self) noexcept
    {
        return self._values.back()._value;
    }

    static constexpr bool empty() noexcept
    {
        return size() == 0;
    }

    static constexpr size_t size()
    {
        return Size;
    }
    
    static constexpr size_t max_size()
    {
        return Size;
    }
    
    friend bool operator==(const aligned_array&, const aligned_array&) = default;
    friend auto operator<=>(const aligned_array&, const aligned_array&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    size_t Size
> using cache_aligned_array = aligned_array<T, Size, std::hardware_destructive_interference_size>;


}
#endif
