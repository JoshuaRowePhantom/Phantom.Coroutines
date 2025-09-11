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

constexpr auto make_task = [](
    auto&& awaitable
)
{
    return ::Phantom::Coroutines::make_task<task>(
        std::forward<decltype(awaitable)>(awaitable));
};

}
#endif
