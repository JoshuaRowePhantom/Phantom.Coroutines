#pragma once
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename T
> concept is_scheduler = requires (T t)
{
    { t.schedule() } -> is_awaitable;
};

}

using detail::is_scheduler;

}