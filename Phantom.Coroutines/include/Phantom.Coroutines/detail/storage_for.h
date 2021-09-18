#include <algorithm>
#include <type_traits>

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
    std::max({ 0, sizeof(TValues)... }),
    std::max({ 0, alignof(TValues)... })
>
{};

}