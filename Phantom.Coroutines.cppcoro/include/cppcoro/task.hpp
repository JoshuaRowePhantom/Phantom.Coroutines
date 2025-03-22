#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_TASK_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_TASK_HPP

#include "Phantom.Coroutines/awaiter_wrapper.h"
#include "Phantom.Coroutines/make_task.h"
#include "Phantom.Coroutines/reusable_task.h"

namespace cppcoro
{

template<
    typename Result = void
> using task = ::Phantom::Coroutines::reusable_task<Result>;

template<
    typename Awaitable
> decltype(auto) make_task(
    Awaitable&& awaitable
)
{
    return ::Phantom::Coroutines::make_task<task>(
        std::forward<Awaitable>(awaitable));
}

}
#endif
