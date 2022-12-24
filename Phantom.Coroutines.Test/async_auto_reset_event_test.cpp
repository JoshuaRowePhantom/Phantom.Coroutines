#include <gtest/gtest.h>
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/async_auto_reset_event.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines
{

TEST(async_auto_reset_event_test, Can_default_initialize)
{
    async_auto_reset_event<> event;
}

TEST(async_auto_reset_event_test, Starts_as_not_set)
{
    async_auto_reset_event<> event;
    ASSERT_FALSE(event.is_set());
}

TEST(async_auto_reset_event_test, Starts_as_not_set_explicitly)
{
    async_auto_reset_event<> event(false);
    ASSERT_FALSE(event.is_set());
}

TEST(async_auto_reset_event_test, Starts_as_set_explicitly)
{
    async_auto_reset_event<> event(true);
    ASSERT_TRUE(event.is_set());
}

TEST(async_auto_reset_event_test, Can_be_reset_after_set)
{
    async_auto_reset_event<> event(true);
    event.reset();
    ASSERT_FALSE(event.is_set());
}

TEST(async_auto_reset_event_test, Set_after_await_continues_one_awaiter_in_reverse_order_and_leaves_reset)
{
    async_auto_reset_event<> event;
    async_scope asyncScope;
    bool complete1 = false;
    bool complete2 = false;
    bool complete3 = false;
    bool allComplete = false;

    auto waitLambda = [&](bool& complete) -> task<>
    {
        suspend_result suspendResult;
        co_await(suspendResult << event);
        EXPECT_EQ(true, suspendResult.did_suspend());
        complete = true;
    };

    asyncScope.spawn(waitLambda(complete1));
    asyncScope.spawn(waitLambda(complete2));
    asyncScope.spawn(waitLambda(complete3));

    auto future = as_future([&]() -> task<>
        {
            co_await asyncScope.join();
            allComplete = true;
        });

    ASSERT_EQ(false, complete1);
    ASSERT_EQ(false, complete2);
    ASSERT_EQ(false, complete3);
    ASSERT_EQ(false, allComplete);
    ASSERT_EQ(false, event.is_set());
    event.set();
    ASSERT_EQ(false, complete1);
    ASSERT_EQ(false, complete2);
    ASSERT_EQ(true, complete3);
    ASSERT_EQ(false, allComplete);
    ASSERT_EQ(false, event.is_set());
    event.set();
    ASSERT_EQ(false, complete1);
    ASSERT_EQ(true, complete2);
    ASSERT_EQ(true, complete3);
    ASSERT_EQ(false, allComplete);
    ASSERT_EQ(false, event.is_set());
    event.set();
    ASSERT_EQ(true, complete1);
    ASSERT_EQ(true, complete2);
    ASSERT_EQ(true, complete3);
    ASSERT_EQ(true, allComplete);
    future.get();
    ASSERT_EQ(false, event.is_set());
}

TEST(async_auto_reset_event_test, Set_before_await_causes_awaiter_to_not_suspend_and_leaves_reset)
{
    async_auto_reset_event<> event;
    std::optional<bool> stateBeforeWait;
    std::optional<bool> stateAfterWait;
    suspend_result suspendResult;

    event.set();

    auto future = as_future([&]() -> task<>
        {
            stateBeforeWait = event.is_set();
            co_await(suspendResult << event);
            stateAfterWait = event.is_set();
        }());

    future.get();
    ASSERT_EQ(true, stateBeforeWait);
    ASSERT_EQ(false, suspendResult.did_suspend());
    ASSERT_EQ(false, stateAfterWait);
}

}