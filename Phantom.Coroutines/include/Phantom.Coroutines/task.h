#pragma once

#include "detail/coroutine.h"
#include "detail/core_task.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "detail/variant_result_storage.h"
#include <concepts>
#include <exception>
#include <type_traits>
#include <variant>
#include "extensible_promise.h"
#include "policies.h"

namespace Phantom::Coroutines::detail
{

template<
    typename Policy
> concept is_task_policy =
is_continuation_type_policy<Policy>;

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
