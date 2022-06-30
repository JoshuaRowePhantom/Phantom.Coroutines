#include <algorithm>
#include <type_traits>
#include "immovable_object.h"

namespace Phantom::Coroutines::detail
{

template<
    size_t Size,
    size_t Alignment
>
struct storage_for_impl
{
    std::aligned_storage_t<Size, Alignment> m_storage;
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
        typename T,
        typename... Args
    > T& emplace(
        Args&&... args
    ) noexcept(noexcept(new T[&m_storage](std::forward<Args>(args)...)))
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
        typename T
    > T& as() noexcept
    {
        return *reinterpret_cast<T*>(&m_storage);
    }

    template<
        typename T
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