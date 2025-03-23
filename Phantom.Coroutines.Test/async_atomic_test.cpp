#include <gtest/gtest.h>
#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_atomic;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.suspend_result;
import Phantom.Coroutines.task;
#else
#include "Phantom.Coroutines/async_atomic.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/task.h"
#endif

namespace Phantom::Coroutines
{

ASYNC_TEST(async_atomic_test, load_returns_initialized_value)
{
    async_atomic<int> atomic(42);
    EXPECT_EQ(42, atomic.load());
    co_return;
}

ASYNC_TEST(async_atomic_test, wait_returns_immediately_if_value_is_not_matched)
{
    async_atomic<int> atomic(42);
    suspend_result suspendResult;
    auto result = co_await(suspendResult << atomic.wait(43));
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(42, result);
}

ASYNC_TEST(async_atomic_test, wait_returns_only_when_exchange_changes_value)
{
    async_scope<> scope;
    async_atomic<int> atomic(42);
    bool complete = false;

    scope.spawn([&]() -> task<>
    {
        auto result = co_await atomic.wait(42);
        EXPECT_EQ(result, 50);
        complete = true;
    });

    EXPECT_EQ(42, atomic.exchange(42));
    EXPECT_EQ(false, complete);

    EXPECT_EQ(42, atomic.exchange(50));
    EXPECT_EQ(true, complete);

    co_await scope.join();
}

ASYNC_TEST(async_atomic_test, wait_returns_only_when_compare_exchange_changes_value)
{
    async_scope<> scope;
    async_atomic<int> atomic(42);
    bool complete = false;

    scope.spawn([&]() -> task<>
    {
        auto result = co_await atomic.wait(42);
        EXPECT_EQ(result, 50);
        complete = true;
    });

    auto expected = 42;
    EXPECT_EQ(true, atomic.compare_exchange_strong(expected, 42));
    EXPECT_EQ(42, expected);
    EXPECT_EQ(false, complete);

    expected = 50;
    EXPECT_EQ(false, atomic.compare_exchange_strong(expected, 42));
    EXPECT_EQ(42, expected);
    EXPECT_EQ(false, complete);
    
    expected = 42;
    EXPECT_EQ(true, atomic.compare_exchange_strong(expected, 50));
    EXPECT_EQ(42, expected);
    EXPECT_EQ(true, complete);

    EXPECT_EQ(50, atomic.load());

    co_await scope.join();
}

}