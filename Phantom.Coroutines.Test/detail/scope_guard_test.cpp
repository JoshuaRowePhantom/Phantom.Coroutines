#include <gtest/gtest.h>
#include <optional>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.scope_guard;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/scope_guard.h"
#endif

using namespace Phantom::Coroutines::detail;

TEST(scope_guard_test, invokes_lambda_on_destruction)
{
    bool invoked = false;
    {
        scope_guard guard{ [&]() { invoked = true; } };
        ASSERT_EQ(false, invoked);
    }
    ASSERT_EQ(true, invoked);
}