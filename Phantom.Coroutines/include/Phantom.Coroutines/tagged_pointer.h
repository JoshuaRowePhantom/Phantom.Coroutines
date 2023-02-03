#pragma once

#include <cstdint>
#include <type_traits>

namespace Phantom::Coroutines
{

template<
    typename Value,
    unsigned short BitCount,
    typename Tag = uintptr_t
>
    requires
    (BitCount < std::bit_width(alignof(Value)))
        || std::same_as<void, Value>
        &&
        std::is_integral_v<Tag>
class tagged_pointer
{
    static constexpr uintptr_t mask = (1 << BitCount) - 1;

    uintptr_t m_value;

    void assign(
        Value* value,
        Tag tag
    )
    {
        assert((reinterpret_cast<uintptr_t>(value) & ~mask) == reinterpret_cast<uintptr_t>(value));
        assert((static_cast<uintptr_t>(tag) & mask) == static_cast<uintptr_t>(tag));

        m_value = reinterpret_cast<uintptr_t>(value) | static_cast<uintptr_t>(tag);
    }

public:
    tagged_pointer() = default;

    tagged_pointer(
        Value* value,
        Tag tag)
    {
        assign(value, tag);
    }

    Value* operator ->() const
    {
        return value();
    }

    Value* value() const
    {
        return reinterpret_cast<Value*>(m_value & ~mask);
    }

    Tag tag() const
    {
        return static_cast<Tag>(m_value & mask);
    }

    friend bool operator==(const tagged_pointer&, const tagged_pointer&) = default;
};

}