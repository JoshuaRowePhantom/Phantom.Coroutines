#include "Phantom.Coroutines/detail/config.h"
#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_latch;
import Phantom.Coroutines.async_scope;
#else
#include "Phantom.Coroutines/async_latch.h"
#include "Phantom.Coroutines/async_scope.h"
#endif
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines
{

ASYNC_TEST(async_latch_test, latch_start_signalled_at_count_0_or_less)
{
    async_latch<> latch1(0);
    async_latch<> latch2(-1);
    co_await latch1;
    co_await latch2;
}

ASYNC_TEST(async_latch_test, latch_releases_at_count_0)
{
    bool completed = false;
    async_scope<> scope;

    async_latch<> latch(2);

    auto lambda = [&]() -> task<>
    {
        co_await latch;
        completed = true;
    };
    scope.spawn(lambda);

    EXPECT_FALSE(completed);
    latch.count_down();
    EXPECT_FALSE(completed);
    latch.count_down();
    EXPECT_TRUE(completed);
    co_await scope.join();
}

ASYNC_TEST(async_latch_test, latch_releases_at_count_less_than_0)
{
    bool completed = false;
    async_scope<> scope;

    async_latch<> latch(3);

    auto lambda = [&]() -> task<>
    {
        co_await latch;
        completed = true;
    };
    scope.spawn(lambda);

    EXPECT_FALSE(completed);
    latch.count_down(2);
    EXPECT_FALSE(completed);
    latch.count_down(2);
    EXPECT_TRUE(completed);
    co_await scope.join();
}

}