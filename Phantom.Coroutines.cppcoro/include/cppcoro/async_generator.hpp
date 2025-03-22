#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_ASYNC_GENERATOR_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_ASYNC_GENERATOR_HPP

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
    using base_generator_type = ::Phantom::Coroutines::async_generator<T>;

public:
    async_generator()
    {}

    async_generator(
        auto&& generator
    ) : 
        base_generator_type{ std::forward<decltype(generator)>(generator) }
    {}

    using iterator = typename base_generator_type::iterator_type;
};

}
#endif
