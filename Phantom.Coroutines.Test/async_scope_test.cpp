#include <gtest/gtest.h>
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

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

TEST(async_scope_test, Can_await_immovable_task)
{
    async_scope<> scope;
    bool completeTask1 = false;
    bool complete = false;

    async_manual_reset_event<> event1;
    scope.spawn([&]() -> task<> 
        { 
            co_await event1; 
            completeTask1 = true;
        }()
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
