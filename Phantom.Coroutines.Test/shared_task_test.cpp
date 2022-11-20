#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "async_test.h"
#include "Phantom.Coroutines/detail/type_traits.h"
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/shared_task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "lifetime_tracker.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(detail::is_awaiter<shared_task_promise<void>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int&>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int&&>::awaiter>);

static_assert(detail::is_awaiter<shared_task_promise<void>::final_suspend_awaiter>);

static_assert(detail::is_awaiter<shared_task_promise<void>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int&>::awaiter>);
static_assert(detail::is_awaiter<shared_task_promise<int&&>::awaiter>);

static_assert(detail::is_awaitable<shared_task<>>);
static_assert(detail::is_awaitable<shared_task<int>>);
static_assert(detail::is_awaitable<shared_task<int&>>);
static_assert(detail::is_awaitable<shared_task<int&&>>);

static_assert(detail::has_co_await_member<shared_task<>>);
static_assert(detail::has_co_await_member<shared_task<>&>);
static_assert(detail::has_co_await_member<shared_task<>&&>);

// Assert the type of awaiter returned by co_await.
static_assert(std::same_as<shared_task_promise<void>::awaiter, decltype(std::declval<shared_task<void>>().operator co_await())>);
static_assert(std::same_as<shared_task_promise<void>::awaiter, decltype(std::declval<shared_task<void>&>().operator co_await())>);
static_assert(std::same_as<shared_task_promise<void>::awaiter, decltype(std::declval<shared_task<void>&&>().operator co_await())>);

static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<>&>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int>&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int&>&>, int&>);

// These assertions verify that co_awaiting an rvalue of a shared_task
// returns a reference to a value. The assumption made is that the caller
// discards the shared_task before the co_await operation, and therefore
// there may be zero references to the shared_task before co_await can return.
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<>>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int&>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string>>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string&>>, std::string&>);

// These assertions verify that co_awaiting an lvalue reference of a shared_task
// returns a reference to a value. The assumption made is that the caller
// maintains the reference to the lvalue shared_task past the co_await operation.
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<>&>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int>&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int&>&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string>&>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string&>&>, std::string&>);

// These assertions verify that co_awaiting an rvalue of a shared_task
// returns a reference to a value. The assumption made is that the caller
// discards the shared_task before the co_await operation, and therefore
// there may be zero references to the shared_task before co_await can return.
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<>&&>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int>&&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int&>&&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string>&&>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<std::string&>&&>, std::string&>);

TEST(shared_task_test, Can_await_void_task)
{
    sync_wait(
        []() -> shared_task<>
        {
            co_return;
        }()
            );
}

TEST(shared_task_test, Can_handle_thrown_exception)
{
    ASSERT_THROW(
        {
            sync_wait(
                []() -> shared_task<>
            {
                throw 5;
                co_return;
            }()
                );
        },
        int);
}

TEST(shared_task_test, Can_await_string_task)
{
    auto result = sync_wait(
        []() -> shared_task<std::string>
        {
            co_return "hello world";
        }());

    ASSERT_EQ("hello world", result);
}

TEST(shared_task_test, Can_return_reference)
{
    int value = 1;

    auto& result = sync_wait(
        [&]() -> shared_task<int&>
        {
            co_return value;
        }());

    ASSERT_EQ(&value, &result);
}

TEST(shared_task_test, Multiple_co_awaits_cause_only_one_invocation)
{
    std::atomic_int invocationCount = 0;

    auto task = [&]() -> shared_task<> 
    { 
        ++invocationCount; 
        co_return; 
    }();

    sync_wait(
        task);

    sync_wait(
        task);

    ASSERT_EQ(1, invocationCount);
}

TEST(shared_task_test, Return_by_value_returns_reference_to_same_object_to_all_calling_awaiters)
{
    auto task = []() -> shared_task<int> { co_return 5; }();

    auto& result1 = sync_wait(
        task);

    auto& result2 = sync_wait(
        task);

    ASSERT_EQ(&result1, &result2);
}

TEST(shared_task_test, Task_destroys_coroutine_if_not_awaited)
{
    lifetime_statistics statistics;
    single_consumer_manual_reset_event event;

    {
        // Create a task and destroy it
        auto myTask = [&, tracker = statistics.tracker()]()->shared_task<>
        {
            tracker.use();
            co_return;
        }();
    }

    ASSERT_EQ(0, statistics.instance_count);
}

TEST(shared_task_test, Task_destroys_coroutine_if_awaited)
{
    lifetime_statistics statistics;
    single_consumer_manual_reset_event event;

    sync_wait([&, tracker = statistics.tracker()]()->shared_task<>
    {
        tracker.use();
        co_return;
    }());

    ASSERT_EQ(0, statistics.instance_count);
}
TEST(shared_task_test, Task_does_destroy_coroutine_if_destroyed_while_suspended)
{
    lifetime_statistics statistics;
    single_consumer_manual_reset_event event;

    {
        // Create and suspend a task, then destroy it.
        auto myTask = [tracker = statistics.tracker(), &event]() -> shared_task<>
        {
            co_await event;
        }();

        auto awaiter = myTask.operator co_await();

        auto coroutine = awaiter.await_suspend(
            std::noop_coroutine()
        );

        // This will reach the first suspend point.
        coroutine.resume();

        // This will destroy the task, but not the promise, since it will have started.
    }

    ASSERT_EQ(0, statistics.instance_count);
}

TEST(shared_task_test, Can_suspend_and_resume)
{
    single_consumer_manual_reset_event event;
    int stage = 0;

    auto future = as_future(
        [&]() -> shared_task<>
        {
            stage = 1;
            co_await event;
            stage = 2;
        });

    ASSERT_EQ(1, stage);
    event.set();
    ASSERT_EQ(2, stage);
}

TEST(shared_task_test, Can_loop_without_stackoverflow)
{
    auto innerTaskLambda = []() -> shared_task<int> { co_return 1; };
    auto outerTaskLambda = [&]() -> shared_task<int>
    {
        auto sum = 0;

        for (int counter = 0; counter < 1000000; counter++)
        {
            sum += co_await innerTaskLambda();
        }

        co_return sum;
    };

    auto actualSum = sync_wait(
        outerTaskLambda());
    ASSERT_EQ(1000000, actualSum);
}
TEST(shared_task_test, Destroys_returned_value_when_co_awaited_as_lvalue)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    sync_wait([&]() -> task<>
        {
            {
                auto task = taskWithReturnValueLambda();
                auto& tracker = co_await task;
                instanceCountBeforeDestruction = statistics.instance_count;
            }
            instanceCountAfterDestruction = statistics.instance_count;
        }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}

TEST(shared_task_test, Destroys_returned_value_when_co_awaited_as_rvalue)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    sync_wait([&]() -> shared_task<>
        {
            {
                co_await taskWithReturnValueLambda();
                instanceCountBeforeDestruction = statistics.instance_count;
            }
            instanceCountAfterDestruction = statistics.instance_count;
        }());

    ASSERT_EQ(0, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}

TEST(shared_task_test, Destroys_thrown_exception)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskLambda = [&]() -> shared_task<>
    {
        throw statistics.tracker();
        co_return;
    };

    sync_wait([&]() -> shared_task<>
        {
            {
                auto task = taskLambda();
                try
                {
                    co_await task;
                }
                catch (lifetime_tracker&)
                {
                    instanceCountBeforeDestruction = statistics.instance_count;
                }
            }
            instanceCountAfterDestruction = statistics.instance_count;
        }());

    // std::exception_ptr implementation is allowed but not required
    // to copy the exception object.  Thus, the lifetime_tracker
    // could have either 1 or 2 as the reference count.
    ASSERT_TRUE(instanceCountBeforeDestruction == 1 || instanceCountBeforeDestruction == 2);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}

ASYNC_TEST(shared_task_test, Result_not_destroyed_until_last_reference_released)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    shared_task<lifetime_tracker> task2 = task1;
    shared_task<lifetime_tracker> task3 = task2;

    auto tracker1 = co_await task1;
    auto tracker2 = co_await task2;
    auto tracker3 = co_await task3;
    EXPECT_EQ(4, statistics.instance_count);

    task1 = shared_task<lifetime_tracker>();
    EXPECT_EQ(4, statistics.instance_count);
    task2 = shared_task<lifetime_tracker>();
    EXPECT_EQ(4, statistics.instance_count);
    task3 = shared_task<lifetime_tracker>();
    EXPECT_EQ(3, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Move_construct_of_task_leaves_old_task_invalid_and_doesnt_increment_reference_count)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    EXPECT_TRUE(task1);
    auto task2 = std::move(task1);

    EXPECT_FALSE(task1);
    EXPECT_TRUE(task2);
    EXPECT_EQ(2, statistics.instance_count);

    task2 = task1;
    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Move_assign_of_task_leaves_old_task_invalid_and_doesnt_increment_reference_count)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    EXPECT_TRUE(task1);
    shared_task<lifetime_tracker> task2;
    EXPECT_TRUE(task1);
    EXPECT_FALSE(task2);

    task2 = std::move(task1);
    EXPECT_FALSE(task1);
    EXPECT_TRUE(task2);

    EXPECT_EQ(2, statistics.instance_count);

    task2 = shared_task<lifetime_tracker>();
    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Copy_asign_reduces_reference_count_of_destination_Task)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    shared_task<lifetime_tracker> task2;
    task1 = task2;

    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Move_asign_reduces_reference_count_of_destination_Task)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    shared_task<lifetime_tracker> task2;
    task1 = std::move(task2);

    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Copy_asign_doesnt_modify_itself)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    task1 = task1;

    EXPECT_EQ(2, statistics.instance_count);
}

ASYNC_TEST(shared_task_test, Move_asign_doesnt_modify_itself)
{
    lifetime_statistics statistics;

    auto taskLambda = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    shared_task<lifetime_tracker> task1 = taskLambda();
    auto tracker = co_await task1;
    EXPECT_EQ(2, statistics.instance_count);

    task1 = std::move(task1);

    EXPECT_EQ(2, statistics.instance_count);
}

TEST(shared_task_test, Default_constructor_produces_invalid_task)
{
    shared_task<> task;
    ASSERT_FALSE(task);
}
