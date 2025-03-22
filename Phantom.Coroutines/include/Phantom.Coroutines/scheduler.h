#ifndef PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_SCHEDULER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "type_traits.h"
#else
import Phantom.Coroutines.type_traits;
#endif

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

using detail::is_scheduler;

}
#endif
