#ifndef PHANTOM_COROUTINES_INCLUDE_NONATOMIC_SHARED_PTR_H
#define PHANTOM_COROUTINES_INCLUDE_NONATOMIC_SHARED_PTR_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <optional>
#include <utility>
#include "detail/config.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace detail
{
struct nonatomic_shared_ptr_control_block
{
    size_t m_referenceCount = 1;
    virtual void destroy_and_deallocate() = 0;
};

template<
    typename T
>
struct nonatomic_shared_ptr_embedded_value_control_block
    :
    public nonatomic_shared_ptr_control_block
{
    std::optional<T> m_value;

    nonatomic_shared_ptr_embedded_value_control_block(
        auto&&... args
    ) :
        m_value(std::in_place, std::forward<decltype(args)>(args)...)
    { }

    void destroy_and_deallocate() override
    {
        delete this;
    }
};

template<
    typename T
>
struct typed_externally_allocated_control_block
    :
    public detail::nonatomic_shared_ptr_control_block
{
    T* m_value;

    typed_externally_allocated_control_block(
        T* value
    ) :
        m_value{ value }
    {
    }

    void destroy_and_deallocate() override
    {
        delete m_value;
    }
};

}

// nonatomic_shared_ptr is like shared_ptr,
// but the reference counting does not use std::atomic.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
>
class nonatomic_shared_ptr
{
    template<
        typename
    >
    friend class nonatomic_shared_ptr;

    detail::nonatomic_shared_ptr_control_block* m_controlBlock = nullptr;
    T* m_value = nullptr;

    template<
        typename U
    > friend nonatomic_shared_ptr<U> make_nonatomic_shared(
        auto&&... args
    )
        requires std::constructible_from<U, decltype(args)...>;

    nonatomic_shared_ptr(
        detail::nonatomic_shared_ptr_embedded_value_control_block<T>* controlBlock
    ) :
        m_value{ std::addressof(*controlBlock->m_value) },
        m_controlBlock{ controlBlock }
    { }

public:
    nonatomic_shared_ptr()
    { }

    nonatomic_shared_ptr(
        std::nullptr_t
    )
    { }

    template<
        typename U
    >
    requires std::convertible_to<U*, T*>
    explicit nonatomic_shared_ptr(
        U* value
    )
    {
        reset(value);
    }

    nonatomic_shared_ptr(
        const nonatomic_shared_ptr& other
    )
    {
        m_controlBlock = other.m_controlBlock;
        m_value = other.m_value;
        if (m_controlBlock)
        {
            ++m_controlBlock->m_referenceCount;
        }
    }
    
    template<
        typename U
    >
    nonatomic_shared_ptr(
        const nonatomic_shared_ptr<U>& other,
        T* value
    )
    {
        if (value)
        {
            assert(other.m_controlBlock);
            m_controlBlock = other.m_controlBlock;
            m_value = value;
            ++m_controlBlock->m_referenceCount;
        }
    }
    
    nonatomic_shared_ptr(
        nonatomic_shared_ptr&& other
    )
    {
        swap(*this, other);
    }

    template<
        typename U
    >
    nonatomic_shared_ptr(
        nonatomic_shared_ptr<U>&& other,
        T* value
    )
    {
        if (value)
        {
            assert(other.m_controlBlock);
            m_controlBlock = other.m_controlBlock;
            m_value = value;
            other.m_controlBlock = nullptr;
            other.m_value = nullptr;
        }
    }

    nonatomic_shared_ptr& operator=(
        const nonatomic_shared_ptr& other
        )
    {
        if (other.m_controlBlock == m_controlBlock)
        {
            return *this;
        }

        reset();
        m_controlBlock = other.m_controlBlock;
        m_value = other.m_value;
        if (m_controlBlock)
        {
            ++m_controlBlock->m_referenceCount;
        }
        return *this;
    }
    
    nonatomic_shared_ptr& operator=(
        nonatomic_shared_ptr&& other
        )
    {
        if (other.m_controlBlock == m_controlBlock)
        {
            return *this;
        }

        reset();
        m_controlBlock = other.m_controlBlock;
        m_value = other.m_value;
        other.m_controlBlock = nullptr;
        other.m_value = nullptr;
        return *this;
    }

    T* operator->() const noexcept
    {
        return m_value;
    }

    T& operator*() const noexcept
    {
        return *m_value;
    }

    T* get() const noexcept
    {
        return m_value;
    }

    explicit operator bool() const noexcept
    {
        return m_value;
    }

    void reset()
    {
        if (m_controlBlock
            &&
            !--m_controlBlock->m_referenceCount)
        {
            m_controlBlock->destroy_and_deallocate();
        }
    }

    void reset(
        std::nullptr_t
    )
    {
        return reset<T>(nullptr);
    }

    template<
        typename U
    >
        requires std::convertible_to<U*, T*>
    void reset(
        U* value
    )
    {
        reset();
        if (value)
        {
            m_controlBlock = new detail::typed_externally_allocated_control_block<U>(value);
            m_value = value;
        }
    }

    ~nonatomic_shared_ptr()
    {
        reset();
    }

    friend auto operator<=>(
        const nonatomic_shared_ptr& left,
        const nonatomic_shared_ptr& right
        )
    {
        return left.m_value <=> right.m_value;
    }

    friend bool operator==(
        const nonatomic_shared_ptr& left,
        const nonatomic_shared_ptr& right
        )
    {
        return left.m_value == right.m_value;
    }

    friend void swap(
        nonatomic_shared_ptr& left,
        nonatomic_shared_ptr& right
    )
    {
        using std::swap;
        swap(left.m_controlBlock, right.m_controlBlock);
        swap(left.m_value, right.m_value);
    }
};

template<
    typename T
>
nonatomic_shared_ptr(T*) -> nonatomic_shared_ptr<T>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> nonatomic_shared_ptr<T> make_nonatomic_shared(
    auto&&... args
)
requires std::constructible_from<T, decltype(args)...>
{
    return nonatomic_shared_ptr<T>
    {
        new detail::nonatomic_shared_ptr_embedded_value_control_block<T>(
            std::forward<decltype(args)>(args)...
        )
    };
}

}
#endif
