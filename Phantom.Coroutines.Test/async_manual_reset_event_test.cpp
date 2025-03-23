#include <gtest/gtest.h>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.suspend_result;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/type_traits.h"
#endif

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(is_awaitable<async_manual_reset_event<>>);
static_assert(is_awaitable<async_manual_reset_event<>&>);
static_assert(is_awaitable<async_manual_reset_event<>&&>);
static_assert(has_co_await_member<async_manual_reset_event<>>);
static_assert(has_co_await_member<async_manual_reset_event<>&>);
static_assert(has_co_await_member<async_manual_reset_event<>&&>);
static_assert(has_await_suspend<decltype(std::declval<async_manual_reset_event<>>().operator co_await())>);

TEST(manual_reset_event_test, Can_default_initialize)
{
    async_manual_reset_event<> event;
}

TEST(manual_reset_event_test, Starts_as_not_set)
{
    async_manual_reset_event<> event;
    ASSERT_FALSE(event.is_set());
}

TEST(manual_reset_event_test, Starts_as_not_set_explicitly)
{
    async_manual_reset_event<> event(false);
    ASSERT_FALSE(event.is_set());
}

TEST(manual_reset_event_test, Starts_as_set_explicitly)
{
    async_manual_reset_event<> event(true);
    ASSERT_TRUE(event.is_set());
}

TEST(manual_reset_event_test, Can_be_reset_after_set)
{
    async_manual_reset_event<> event(true);
    event.reset();
    ASSERT_FALSE(event.is_set());
}

TEST(manual_reset_event_test, Set_after_await_continues_awaiters_and_leaves_set)
{
    async_manual_reset_event<> event;
    async_scope<> asyncScope;
    bool complete = false;

    auto waitLambda = [&]() -> task<>
    {
        suspend_result suspendResult;
        co_await(suspendResult << event);
        EXPECT_EQ(true, suspendResult.did_suspend());
    };

    asyncScope.spawn(waitLambda());
    asyncScope.spawn(waitLambda());
    asyncScope.spawn(waitLambda());
    
    auto future = as_future([&]() -> task<>
        {
            co_await asyncScope.join();
            complete = true;
        });

    ASSERT_EQ(false, complete);
    event.set();
    ASSERT_EQ(true, complete);
    future.get();
    ASSERT_EQ(true, event.is_set());
}

TEST(manual_reset_event_test, Set_before_await_causes_awaiter_to_not_suspend_and_leaves_set)
{
    async_manual_reset_event<> event;
    std::optional<bool> stateBeforeWait;
    std::optional<bool> stateAfterWait;
    suspend_result suspendResult;

    event.set();

    auto future = as_future([&]() -> task<>
        {
            stateBeforeWait = event.is_set();
            co_await(suspendResult << event);
            stateAfterWait = event.is_set();
        });

    future.get();
    ASSERT_EQ(true, stateBeforeWait);
    ASSERT_EQ(false, suspendResult.did_suspend());
    ASSERT_EQ(true, stateAfterWait);
}

