#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_latch;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_latch.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/task.h"
#endif

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