#ifndef PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "type_traits.h"
#endif

#include "detail/assert_is_configured_module.h"

namespace Phantom::Coroutines
{
namespace detail
{

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
