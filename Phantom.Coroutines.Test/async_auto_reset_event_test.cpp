#include <gtest/gtest.h>
#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_auto_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.static_thread_pool;
#else
#include "Phantom.Coroutines/async_auto_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/static_thread_pool.h"
#endif
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines
{
static_assert(is_awaitable<async_auto_reset_event<>>);
static_assert(is_awaitable<async_auto_reset_event<>&>);

class async_auto_reset_event_test : public ::testing::Test
{
protected:
    static_thread_pool<> waiterPool;
    static_thread_pool<> setterPool = static_thread_pool<>(std::max<size_t>(2U, waiterPool.thread_count() / 2));
};

ASYNC_TEST_F(async_auto_reset_event_test, Can_default_initialize)
{
    async_auto_reset_event<> event;
    co_return;
}

ASYNC_TEST_F(async_auto_reset_event_test, Starts_as_not_set)
{
    async_auto_reset_event<> event;
    EXPECT_FALSE(event.is_set());
    co_return;
}

ASYNC_TEST_F(async_auto_reset_event_test, Starts_as_not_set_explicitly)
{
    async_auto_reset_event<> event(false);
    EXPECT_FALSE(event.is_set());
    co_return;
}

ASYNC_TEST_F(async_auto_reset_event_test, Starts_as_set_explicitly)
{
    async_auto_reset_event<> event(true);
    EXPECT_TRUE(event.is_set());
    co_return;
}

ASYNC_TEST_F(async_auto_reset_event_test, Can_be_reset_after_set)
{
    async_auto_reset_event<> event(true);
    event.reset();
    EXPECT_FALSE(event.is_set());
    co_return;
}

ASYNC_TEST_F(async_auto_reset_event_test, Set_after_await_continues_one_awaiter_in_order_and_leaves_reset)
{
    async_auto_reset_event<> event;
    async_scope<> asyncScope;
    async_scope<> outerScope;
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

    outerScope.spawn([&]() -> task<>
    {
        co_await asyncScope.join();
        allComplete = true;
    });

    EXPECT_EQ(false, complete1);
    EXPECT_EQ(false, complete2);
    EXPECT_EQ(false, complete3);
    EXPECT_EQ(false, allComplete);
    EXPECT_EQ(false, event.is_set());
    event.set();
    EXPECT_EQ(true, complete1);
    EXPECT_EQ(false, complete2);
    EXPECT_EQ(false, complete3);
    EXPECT_EQ(false, allComplete);
    EXPECT_EQ(false, event.is_set());
    event.set();
    EXPECT_EQ(true, complete1);
    EXPECT_EQ(true, complete2);
    EXPECT_EQ(false, complete3);
    EXPECT_EQ(false, allComplete);
    EXPECT_EQ(false, event.is_set());
    event.set();
    EXPECT_EQ(true, complete1);
    EXPECT_EQ(true, complete2);
    EXPECT_EQ(true, complete3);
    EXPECT_EQ(true, allComplete);
    co_await outerScope.join();
    EXPECT_EQ(false, event.is_set());
}

ASYNC_TEST_F(async_auto_reset_event_test, Set_before_await_causes_awaiter_to_not_suspend_and_leaves_reset)
{
    async_auto_reset_event<> event;
    std::optional<bool> stateBeforeWait;
    std::optional<bool> stateAfterWait;
    suspend_result suspendResult;

    event.set();

    auto lambda = [&]() -> task<>
    {
        stateBeforeWait = event.is_set();
        co_await(suspendResult << event);
        stateAfterWait = event.is_set();
    };

    co_await lambda();
    EXPECT_EQ(true, stateBeforeWait);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(false, stateAfterWait);
}

ASYNC_TEST_F(async_auto_reset_event_test, reentrant_set_leaves_signalled)
{
    async_auto_reset_event<> event;
    auto lambda = [&]() -> task<>
    {
        co_await event;
        event.set();
        event.set();
        event.set();
        co_await event;
    };
    async_scope<> scope;
    scope.spawn(lambda);
    event.set();
    co_await scope.join();
}

ASYNC_TEST_F(async_auto_reset_event_test, can_destroy_from_resumption_of_coroutine)
{
    async_auto_reset_event<>* innerEventPointer;

    auto lambda = [&]() -> task<>
    {
        async_auto_reset_event<> event;
        innerEventPointer = &event;
        co_await event;
    };
    async_scope<> scope;
    scope.spawn(lambda);
    innerEventPointer->set();
    co_await scope.join();
}

ASYNC_TEST_F(async_auto_reset_event_test, DISABLED_can_loop_without_stack_overflow)
{
    async_auto_reset_event<> event;

    auto lambda = [&]() -> task<>
    {
        co_await event;
        event.set();
    };

    async_scope<> scope;
    for (auto counter = 0; counter < 10000; ++counter)
    {
        scope.spawn(lambda());
    }

    event.set();
    co_await scope.join();
}

ASYNC_TEST_F(async_auto_reset_event_test, DISABLED_Many_iterations)
{
    for (auto outerCounter = 0; outerCounter < 10; outerCounter++)
    {
        async_auto_reset_event<> event;
        async_scope<> asyncScope;
        std::atomic<int> remainingThreads;

        auto waiter = [&](int waiterNumber) -> task<>
        {
            ++remainingThreads;
            for (auto counter = 0; counter < 10000; counter++)
            {
                co_await event;
                co_await waiterPool.schedule();
            }
            --remainingThreads;

            //std::cerr << "waiter " << waiterNumber << " done.\n";
        };

        auto setter = [&](int setterNumber) -> task<>
        {
            while (remainingThreads.load())
            {
                event.set();
                co_await setterPool.schedule();
            }

            //std::cerr << "setter " << setterNumber << " done.\n";
        };

        for (auto counter = 0; counter < 50; counter++)
        {
            asyncScope.spawn(waiter(counter));
        }

        for (auto counter = 0; counter < 50; counter++)
        {
            asyncScope.spawn(setter(counter));
        }

        co_await asyncScope.join();
        //std::cerr << "All done!\n";
    }
}

}