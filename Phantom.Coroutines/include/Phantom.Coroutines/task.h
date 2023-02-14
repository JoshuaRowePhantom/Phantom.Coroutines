#pragma once

#include <concepts>
#include "policies.h"
#include "detail/core_task.h"

namespace Phantom::Coroutines::detail
{

template<
    typename Policy
> concept is_task_policy =
is_continuation_type_policy<Policy>
|| is_concrete_policy<Policy, single_awaiter>
|| is_concrete_policy<Policy, noop_on_destroy>
|| is_concrete_policy<Policy, await_is_not_cancellable>;

template<
    typename Result,
    is_task_policy ... Policies
> 
using task_promise = core_task_promise<
    Result,
    select_continuation_type<
        Policies..., 
        continuation_type<coroutine_handle<>>>,
    core_non_reusable_task_promise_base
>;

template<
    typename Promise
> using basic_task = core_task<Promise>;

template<
    typename Result = void,
    is_task_policy... Policies
> using task = basic_task<task_promise<Result, Policies...>>;

}

namespace Phantom::Coroutines
{
using detail::basic_task;
using detail::task;
using detail::task_promise;

}
