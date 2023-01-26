#pragma once

#include "Phantom.Coroutines/async_generator.h"

namespace cppcoro
{
template<
    typename T
>
class async_generator
    :
    public ::Phantom::Coroutines::async_generator<T>
{
    using ::Phantom::Coroutines::async_generator<T>::async_generator;

    using iterator = typename ::Phantom::Coroutines::async_generator<T>::iterator_type;
};

}
