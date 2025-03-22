#ifndef PHANTOM_COROUTINES_INCLUDE_MAKE_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_MAKE_TASK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "task.h"
#include "type_traits.h"
#endif

#include "detail/assert_is_configured_module.h"

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    template <typename Result> typename Task = task,
    typename Awaitable
> auto make_task(
    Awaitable&& awaitable
)
{
    using result_task_type = Task<detail::remove_rvalue_reference_t<awaitable_result_type_t<Awaitable>>>;

    if constexpr (std::is_lvalue_reference_v<Awaitable>)
    {
        return [](Awaitable awaitable) -> result_task_type
        {
            co_return co_await awaitable;
        }(awaitable);
    }
    else
    {
        return [](Awaitable awaitable) -> result_task_type
        {
            co_return co_await std::move(awaitable);
        }(std::move(awaitable));
    }
}

}
#endif
