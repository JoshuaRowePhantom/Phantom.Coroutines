#include <gtest/gtest.h>
#include "async_test.h"
#include "Phantom.Coroutines/async_sequence_barrier.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.reusable_task;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.task;
#else
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/reusable_task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#endif

using namespace Phantom::Coroutines;

TEST(async_scope_test, Joining_empty_completes_immediately)
{
    async_scope<> scope;
    sync_wait([&]() -> task<>
        {
            co_await scope.join();
        }());
}

TEST(async_scope_test, Joining_waits_for_incomplete_tasks)
{
    async_scope<> scope;
    async_manual_reset_event<> event1;
    async_manual_reset_event<> event2;
    async_manual_reset_event<> event3;
    bool complete = false;

    event1.set();
    scope.spawn(event1);
    scope.spawn(event2);
    scope.spawn(event3);
    
    auto future = as_future([&]() -> task<>
        {
            co_await scope.join();
            complete = true;
        }());

    ASSERT_EQ(false, complete);
    event2.set();
    ASSERT_EQ(false, complete);
    event3.set();
    ASSERT_EQ(true, complete);
    future.get();
}

TEST(async_scope_test, Joining_completes_immediately_if_all_tasks_already_complete)
{
    async_scope<> scope;
    async_manual_reset_event<> event1;
    async_manual_reset_event<> event2;
    async_manual_reset_event<> event3;
    bool complete = false;

    event1.set();
    scope.spawn(event1);
    scope.spawn(event2);
    scope.spawn(event3);

    ASSERT_EQ(false, complete);
    event2.set();
    ASSERT_EQ(false, complete);
    event3.set();
    ASSERT_EQ(false, complete);

    auto future = as_future([&]() -> task<>
        {
            co_await scope.join();
            complete = true;
        }());

    ASSERT_EQ(true, complete);
    future.get();
}

TEST(async_scope_test, Can_await_non_copyable_task_by_lambda)
{
    async_scope<> scope;
    bool completeTask1 = false;
    bool complete = false;

    async_manual_reset_event<> event1;
    scope.spawn([&]() -> task<> 
        { 
            co_await event1; 
            completeTask1 = true;
        }
    );

    auto future = as_future([&]() -> task<>
        {
            co_await scope.join();
            complete = true;
        }());

    ASSERT_EQ(false, complete);
    ASSERT_EQ(false, completeTask1);
    event1.set();
    ASSERT_EQ(true, completeTask1);
    ASSERT_EQ(true, complete);
    future.get();
}

ASYNC_TEST(async_scope_test, Can_await_non_copyable_task_by_value)
{
    async_scope<> scope;
    bool completeTask1 = false;
    bool completeTask2 = false;
    async_sequence_barrier<size_t> barrier;

    auto lambda = [&]() -> reusable_task<>
    {
        co_await barrier.wait_until_published(1);
        completeTask1 = true;
        co_await barrier.wait_until_published(2);
        completeTask2 = true;
    };

    scope.spawn(lambda());

    EXPECT_EQ(false, completeTask1);
    barrier.publish(1);
    EXPECT_EQ(true, completeTask1);
    EXPECT_EQ(false, completeTask2);
    barrier.publish(2);
    EXPECT_EQ(true, completeTask2);
    co_await scope.join();
}

ASYNC_TEST(async_scope_test, Can_spawn_during_join)
{
    async_scope<> scopeToTest;
    async_scope<> scope2;
    async_manual_reset_event<> continueEvent;
    bool completedLambda1 = false;

    auto lambda1 = [&]() -> task<>
        {
            completedLambda1 = true;
            co_return;
        };

    auto lambda2 = [&]() -> task<>
        {
            co_await continueEvent;
            scopeToTest.spawn(lambda1());
            co_return;
        };

    scopeToTest.spawn(
        lambda2());

    scope2.spawn(
        scopeToTest.join());

    continueEvent.set();

    co_await scope2.join();
    EXPECT_EQ(completedLambda1, true);
}
