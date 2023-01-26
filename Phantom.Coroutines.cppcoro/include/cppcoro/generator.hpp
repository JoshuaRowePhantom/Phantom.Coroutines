#pragma once

#include "Phantom.Coroutines/generator.h"

namespace cppcoro
{
template<
    typename T
>
using generator = ::Phantom::Coroutines::generator<T>;
}