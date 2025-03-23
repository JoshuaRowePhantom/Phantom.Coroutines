#ifndef PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> concept is_scheduler = requires (T t)
{
    { t.schedule() } -> is_awaitable;
};

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_scheduler;

}
#endif
