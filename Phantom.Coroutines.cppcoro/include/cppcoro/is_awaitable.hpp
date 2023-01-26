#include "Phantom.Coroutines/type_traits.h"

namespace cppcoro
{

template<
    typename T
>
using is_awaitable = std::bool_constant<
    ::Phantom::Coroutines::is_awaitable<T>
>;

template<typename T>
constexpr bool is_awaitable_v = is_awaitable<T>::value;
}
