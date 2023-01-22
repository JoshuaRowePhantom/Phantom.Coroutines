#pragma once
#include "extensible_promise.h"

namespace Phantom::Coroutines
{

template<
    typename Promise,
    typename Allocator
> class promise_allocator
    :
    public derived_promise<Promise>
{
public:
    using allocator_type = Allocator;
    using allocator_traits = std::allocator_traits<Allocator>;

private:
    static constexpr bool allocator_is_empty = allocator_traits::is_always_equal::value;
    using char_allocator_type = typename allocator_traits::template rebind_alloc<char>;

    static constexpr size_t extra_allocation_size =
        allocator_is_empty
        ?
        0
        :
        (sizeof(Allocator) + __STDCPP_DEFAULT_NEW_ALIGNMENT__ - 1) / __STDCPP_DEFAULT_NEW_ALIGNMENT__ * __STDCPP_DEFAULT_NEW_ALIGNMENT__;

    static void* allocate(
        allocator_type& allocator,
        size_t size
    )
    {
        char_allocator_type charAllocator{ allocator };
        size += extra_allocation_size;

        char* memory;

        if constexpr (has_get_return_object_on_allocation_failure<Promise>)
        {
            try
            {
                memory = charAllocator.allocate(size);
                if (!memory)
                {
                    return nullptr;
                }
            }
            catch (const std::bad_alloc&)
            {
                return nullptr;
            }
        }
        else
        {
            memory = charAllocator.allocate(size);
        }

        if constexpr (!allocator_is_empty)
        {
            if (memory)
            {
                new (memory) char_allocator_type(std::move(charAllocator));
            }
        }
        return memory + extra_allocation_size;
    }

    static void deallocate(
        void* location,
        size_t size
    )
    {
        auto memory = reinterpret_cast<char*>(location) - extra_allocation_size;
        size += extra_allocation_size;
        if constexpr (allocator_is_empty)
        {
            char_allocator_type().deallocate(memory);
        }
        else
        {
            auto previousAllocator = reinterpret_cast<char_allocator_type*>(memory);
            char_allocator_type allocator(
                std::move(*previousAllocator));
            previousAllocator->~char_allocator_type();
            allocator.deallocate(memory, size);
        }
    }

public:
    using allocator_type = Allocator;
    using derived_promise<Promise>::derived_promise;

    static void* operator new(
        size_t size,
        allocator_type& allocator,
        auto&... args)
    {
        return allocate(allocator, size);
    }

    static void* operator new(
        size_t size,
        auto& arg,
        auto&... args
        )
        requires !std::same_as<std::nothrow_t, std::remove_cvref_t<decltype(arg)>>
    {
        return operator new(
            size,
            args...);
    }

    static void* operator new(
        size_t size
        )
        requires std::is_default_constructible_v<allocator_type>
    {
        allocator_type allocator;
        return operator new(
            size,
            allocator);
    }

    static void operator delete(
        void* location,
        size_t size
        )
    {
        return deallocate(location, size);
    }
};

}
