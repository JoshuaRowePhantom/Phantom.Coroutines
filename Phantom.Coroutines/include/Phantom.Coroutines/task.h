#ifndef PHANTOM_COROUTINES_INCLUDE_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_TASK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include "detail/config_macros.h"
#include "detail/core_task.h"
#include "detail/coroutine.h"
#include "policies.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Policy
> concept is_task_policy =
is_continuation_type_policy<Policy>
|| is_concrete_policy<Policy, single_awaiter>
|| is_concrete_policy<Policy, noop_on_destroy>
|| is_concrete_policy<Policy, await_is_not_cancellable>;

PHANTOM_COROUTINES_MODULE_EXPORT
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

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> using basic_task = core_task<Promise>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result = void,
    is_task_policy... Policies
> using task = basic_task<task_promise<Result, Policies...>>;

}

namespace Phantom::Coroutines
{
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_task;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::task;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::task_promise;

}

#endif
