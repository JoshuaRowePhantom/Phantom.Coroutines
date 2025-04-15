#ifndef PHANTOM_COROUTINES_INCLUDE_RESUSABLE_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_RESUSABLE_TASK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <utility>
#include "detail/core_task.h"
#include "detail/coroutine.h"
#include "policies.h"
#else
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Policy
> concept is_reusable_task_policy =
is_continuation_type_policy<Policy>
|| is_concrete_policy<Policy, single_awaiter>
|| is_concrete_policy<Policy, noop_on_destroy>
|| is_concrete_policy<Policy, await_is_not_cancellable>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    is_reusable_task_policy ... Policies
>
using reusable_task_promise = core_task_promise<
    Result,
    select_continuation_type
    <
        Policies...,
        default_continuation_type
    >,
    core_reusable_task_promise_base
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> using basic_reusable_task = core_task<Promise>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result = void,
    is_reusable_task_policy... Policies
> using reusable_task = basic_reusable_task<reusable_task_promise<Result, Policies...>>;

// Make a reusable_task from a value. The resulting
// task will already be completed, and can be used and reused
// as many times as desired, including by multiple threads.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    typename Task = reusable_task<Result>
> Task make_reusable_task_from_value(
    Result&& result
)
{
    auto lambda = [&]() -> Task
    {
        co_return std::forward<Result>(result);
    };
    auto task = lambda();
    auto awaiter = task.when_ready();
    awaiter.await_ready();
    awaiter.await_suspend(noop_coroutine()).resume();

    return std::move(task);
}

// Make a completed reusable_task that returns void. The resulting
// task will already be completed, and can be used and reused
// as many times as desired, including by multiple threads.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Task = reusable_task<>
> Task make_reusable_task_from_void()
{
    auto lambda = [&]() -> Task
    {
        co_return;
    };
    auto task = lambda();
    auto awaiter = task.when_ready();
    awaiter.await_ready();
    awaiter.await_suspend(noop_coroutine()).resume();

    return std::move(task);
}

}

namespace Phantom::Coroutines
{
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_reusable_task;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::reusable_task_promise;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::reusable_task;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::make_reusable_task_from_value;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::make_reusable_task_from_void;

}

#endif
