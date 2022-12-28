#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/scope_guard.h"
#include <optional>

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