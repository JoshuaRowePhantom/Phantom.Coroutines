#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.non_copyable;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/non_copyable.h"
#endif

#include <concepts>

namespace
{
static_assert(!std::is_copy_constructible_v<Phantom::Coroutines::detail::noncopyable>);
static_assert(!std::is_move_constructible_v<Phantom::Coroutines::detail::noncopyable>);
static_assert(!std::is_copy_assignable_v<Phantom::Coroutines::detail::noncopyable>);
static_assert(!std::is_move_assignable_v<Phantom::Coroutines::detail::noncopyable>);
}
