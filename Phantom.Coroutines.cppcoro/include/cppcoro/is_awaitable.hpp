#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_IS_AWAITABLE_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_IS_AWAITABLE_HPP

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
#endif
