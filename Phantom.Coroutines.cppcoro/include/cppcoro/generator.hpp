#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_GENERATOR_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_GENERATOR_HPP

#include "Phantom.Coroutines/generator.h"

namespace cppcoro
{
template<
    typename T
>
using generator = ::Phantom::Coroutines::generator<T>;
}
#endif
