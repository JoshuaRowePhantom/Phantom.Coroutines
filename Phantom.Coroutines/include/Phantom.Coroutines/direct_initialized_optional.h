#ifndef PHANTOM_COROUTINES_INCLUDE_DIRECT_INITIALIZED_OPTIONAL_H
#define PHANTOM_COROUTINES_INCLUDE_DIRECT_INITIALIZED_OPTIONAL_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <type_traits>
#include <utility>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> class direct_initialized_optional
{
    union
    {
        T value;
    };
    bool hasValue = false;

public:
    direct_initialized_optional()
    {}

    direct_initialized_optional(
        auto&&... args
    ) noexcept(noexcept(emplace(std::forward<decltype(args)>(args)...)))
    {
        emplace(std::forward<decltype(args)>(args)...);
    }

    direct_initialized_optional(
        direct_initialized_optional& other
    )
    {
        if (other.hasValue)
        {
            new (std::addressof(value)) T(*other);
            hasValue = true;
        }
    }

    direct_initialized_optional(
        const direct_initialized_optional& other
    )
    {
        if (other.hasValue)
        {
            new (std::addressof(value)) T(*other);
            hasValue = true;
        }
    }
    

    direct_initialized_optional(
        direct_initialized_optional&& other
    )
        noexcept(noexcept(
            new (std::addressof(value)) T(std::move(*other))
        ))
    {
        if (other.hasValue)
        {
            new (std::addressof(value)) T(std::move(*other));
            hasValue = true;
        }
    }

    direct_initialized_optional& operator=(
        const direct_initialized_optional& other
        )
    {
        if (other.hasValue
            && hasValue)
        {
            **this = *other;
        }
        else
        {
            reset();
            if (other.hasValue)
            {
                new (std::addressof(value)) T(*other);
                hasValue = true;
            }
        }
        return *this;
    }

    direct_initialized_optional& operator=(
        direct_initialized_optional&& other
        )
    {
        if (other.hasValue
            && hasValue)
        {
            **this = std::move(*other);
        }
        else
        {
            reset();
            if (other.hasValue)
            {
                new (std::addressof(value)) T(std::move(*other));
                hasValue = true;
            }
        }
        return *this;
    }

    ~direct_initialized_optional()
    {
        reset();
    }

    void emplace(
        auto&&... args
    ) noexcept(noexcept(
        new (std::addressof(value)) T(std::forward<decltype(args)>(args)...)
        ))
    {
        reset();
        new (std::addressof(value)) T(std::forward<decltype(args)>(args)...);
        hasValue = true;
    }
    
    void emplace(
        std::invocable<> auto&& initializer
    ) noexcept(noexcept(
        new (std::addressof(value)) T(std::forward<decltype(initializer)>(initializer)())
        ))
    {
        reset();
        new (std::addressof(value)) T(std::forward<decltype(initializer)>(initializer)());
        hasValue = true;
    }

    explicit operator bool() const noexcept
    {
        return hasValue;
    }

    bool has_value() const noexcept
    {
        return hasValue;
    }

    auto& operator*() noexcept
    {
        return value;
    }

    const T& operator*() const noexcept
    {
        return value;
    }

    auto operator->() noexcept
    {
        return std::addressof(value);
    }

    auto operator->() const noexcept
    {
        return std::addressof(value);
    }

    void reset() noexcept
    {
        if (hasValue)
        {
            value.~T();
            hasValue = false;
        }
    }
};

}
#endif
