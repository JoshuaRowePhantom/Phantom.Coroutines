#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <algorithm>
#include <type_traits>
#include "detail/immovable_object.h"
#include "../type_traits.h"
#endif

namespace Phantom::Coroutines::detail
{

template<
    size_t Size,
    size_t Alignment
>
struct storage_for_impl
{
    alignas(Alignment) char m_storage[Size];
};

template<
>
struct storage_for_impl<
    0,
    0
>
{
    inline static char m_storage;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... TValues
> struct storage_for
    :
public storage_for_impl<
    std::max({ static_cast<size_t>(0), sizeof(TValues)... }),
    std::max({ static_cast<size_t>(0), alignof(TValues)... })
>,
private immovable_object
{
    using storage_for::storage_for_impl::m_storage;

    template<
        is_in_types<TValues...> T,
        typename... Args
    > T& emplace(
        Args&&... args
    ) noexcept(noexcept(new (&m_storage)T(std::forward<Args>(args)...)))
    {
        if constexpr (sizeof(T) == 0)
        {
            return;
        }
        else
        {
            new (&m_storage)T(std::forward<Args>(args)...);
        }
        return as<T>();
    }

    template<
        is_in_types<TValues...> T
    > T& as() noexcept
    {
        return *reinterpret_cast<T*>(&m_storage);
    }

    template<
        is_in_types<TValues...> T
    > void destroy()
    {
        if constexpr (sizeof(T) == 0)
        {
            return;
        }
        else
        {
            as<T>().~T();
        }
    }
};

}