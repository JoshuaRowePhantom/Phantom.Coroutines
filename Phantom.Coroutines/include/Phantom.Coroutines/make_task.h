#ifndef PHANTOM_COROUTINES_INCLUDE_MAKE_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_MAKE_TASK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <type_traits>
#include <utility>
#include "shared_task.h"
#include "task.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

template<
    typename Task,
    typename Awaitable
> Task make_task_wrapper_implementation(
    Awaitable awaitable
)
{
    co_return co_await std::forward<Awaitable>(awaitable);
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    template <typename Result> typename Task
> constexpr auto make_task_wrapper = []<typename Awaitable>(
    Awaitable&& awaitable
    )
{
    using result_task_type = Task<detail::remove_rvalue_reference_t<awaitable_result_type_t<Awaitable>>>;
    return make_task_wrapper_implementation<
        result_task_type,
        Awaitable
    >(
        std::forward<Awaitable>(awaitable));
};

PHANTOM_COROUTINES_MODULE_EXPORT
constexpr auto make_task = make_task_wrapper<task>;

PHANTOM_COROUTINES_MODULE_EXPORT
constexpr auto make_shared_task = make_task_wrapper<shared_task>;

}
#endif
