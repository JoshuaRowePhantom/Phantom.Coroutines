#include <gtest/gtest.h>
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(single_consumer_manual_reset_event_test, Can_default_initialize)
{
    single_consumer_manual_reset_event event;
}

TEST(single_consumer_manual_reset_event_test, Starts_as_not_set)
{
    single_consumer_manual_reset_event event;
    ASSERT_FALSE(event.is_set());
}

TEST(single_consumer_manual_reset_event_test, Starts_as_not_set_explicitly)
{
    single_consumer_manual_reset_event event(false);
    ASSERT_FALSE(event.is_set());
}

TEST(single_consumer_manual_reset_event_test, Starts_as_set_explicitly)
{
    single_consumer_manual_reset_event event(true);
    ASSERT_TRUE(event.is_set());
}

TEST(single_consumer_manual_reset_event_test, Can_be_reset_after_set)
{
    single_consumer_manual_reset_event event(true);
    event.reset();
    ASSERT_FALSE(event.is_set());
}

TEST(single_consumer_manual_reset_event_test, Set_after_await_continues_awaiter_and_leaves_set)
{
    single_consumer_manual_reset_event event;
    std::optional<bool> stateBeforeWait;
    std::optional<bool> stateAfterWait;
    suspend_result suspendResult;

    auto lambda = [&]() -> task<>
    {
        stateBeforeWait = event.is_set();
        co_await(suspendResult << event);
        stateAfterWait = event.is_set();
    };

    auto future = as_future(lambda());

    event.set();
    future.get();
    ASSERT_EQ(false, stateBeforeWait);
    ASSERT_EQ(true, suspendResult.did_suspend());
    ASSERT_EQ(true, stateAfterWait);
}

TEST(single_consumer_manual_reset_event_test, Set_before_await_causes_awaiter_to_not_suspend_and_leaves_set)
{
    single_consumer_manual_reset_event event;
    std::optional<bool> stateBeforeWait;
    std::optional<bool> stateAfterWait;
    suspend_result suspendResult;

    event.set();

    auto future = as_future([&]() -> task<>
    {
        stateBeforeWait = event.is_set();
        co_await (suspendResult << event);
        stateAfterWait = event.is_set();
    });

    future.get();
    ASSERT_EQ(true, stateBeforeWait);
    ASSERT_EQ(false, suspendResult.did_suspend());
    ASSERT_EQ(true, stateAfterWait);
}
