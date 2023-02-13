#pragma once

#include <concepts>
#include "policies.h"
#include "detail/core_task.h"

namespace Phantom::Coroutines::detail
{

template<
    typename Policy
> concept is_reusable_task_policy =
is_continuation_type_policy<Policy>;

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

template<
    typename Promise
> using basic_reusable_task = core_task<Promise>;

template<
    typename Result = void,
    is_reusable_task_policy... Policies
> using reusable_task = basic_reusable_task<reusable_task_promise<Result, Policies...>>;

}

namespace Phantom::Coroutines
{
using detail::basic_reusable_task;
using detail::reusable_task_promise;
using detail::reusable_task;

}
