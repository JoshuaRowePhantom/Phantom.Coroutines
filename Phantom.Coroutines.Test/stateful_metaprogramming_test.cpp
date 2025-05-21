#include <gtest/gtest.h>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.stateful_metaprogramming;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/stateful_metaprogramming.h"
#endif

namespace Phantom::Coroutines::stateful_metaprogramming
{

struct test_label {};
struct test_value {};
static_assert(!has_state<test_label>);
static_assert(write_state<test_label, test_value>);
static_assert(has_state<test_label>);
static_assert(std::same_as<test_value, read_state<test_label>>);

}