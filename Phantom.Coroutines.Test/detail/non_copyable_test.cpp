#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.non_copyable;
#else
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
