#pragma once

#include "atomic_state.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TValue
> 
class promise
{
public:
    template<
        typename ... TArguments
    > void emplace(
        TArguments...&& arguments
    )
    {

    }
};

template<
    typename... TValues
>
class promise<
    std::variant<TValues...>
>
{
public:
    template<
        typename ... TArguments
    > void emplace(
        TArguments...&& arguments
    )
    {

    }
};
}

using detail::promise;
}
