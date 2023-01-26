#pragma once

#include "Phantom.Coroutines/sequence_barrier.h"

namespace cppcoro
{

template<
    typename Value
> using sequence_barrier = ::Phantom::Coroutines::sequence_barrier<Value>;

}