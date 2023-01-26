#pragma once

#include "Phantom.Coroutines/make_task.h"
#include "Phantom.Coroutines/shared_task.h"

namespace cppcoro
{

template<
    typename T = void
>
using shared_task = Phantom::Coroutines::shared_task<T>;

template<
    typename Awaitable
> decltype(auto) make_shared_task(
    Awaitable&& awaitable
)
{
    return ::Phantom::Coroutines::make_task<shared_task>(
        std::forward<Awaitable>(awaitable));
}

}
