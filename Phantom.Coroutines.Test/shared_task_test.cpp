#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/type_traits.h"
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/shared_task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "lifetime_tracker.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(detail::is_awaiter<task_awaiter<>>);
static_assert(detail::is_awaiter<task_awaiter<int>>);
static_assert(detail::is_awaiter<task_awaiter<int&>>);

static_assert(detail::is_awaitable<shared_task<>>);
static_assert(detail::is_awaitable<shared_task<int>>);
static_assert(detail::is_awaitable<shared_task<int&>>);

static_assert(detail::has_co_await<shared_task<>&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<>&&>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<shared_task<int&>>, int&>);

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

TEST(shared_task_test, Returned_object_is_by_lvalue_reference_to_caller_in_rvalue_context)
{
    lifetime_statistics statistics;
    std::optional<lifetime_statistics> intermediateStatistics;

    auto myLambda = [&](lifetime_tracker& tracker)
    {};

    auto myInnerTask = [&]() -> shared_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto myOuterTask = [&]() -> shared_task<>
    {
        myLambda(co_await std::move(myInnerTask()));
        intermediateStatistics = statistics;
    };

    sync_wait(
        myOuterTask());

    ASSERT_EQ(1, intermediateStatistics->move_construction_count);
    ASSERT_EQ(0, intermediateStatistics->copy_construction_count);
    ASSERT_EQ(0, intermediateStatistics->instance_count);
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

TEST(shared_task_test, Task_destroys_coroutine_if_destroyed_while_suspended)
{
    lifetime_statistics statistics;
    single_consumer_manual_reset_event event;

    {
        // Create and suspend a task, then destroy it.
        auto myTask = [&]() -> shared_task<>
        {
            auto tracker = statistics.tracker();
            co_await event;
        }();

        auto awaiter = std::move(myTask).operator co_await();

        auto coroutine = awaiter.await_suspend(
            std::noop_coroutine()
        );

        // This will reach the first suspend point.
        coroutine.resume();

        // This will destroy the awaiter.
    }

    ASSERT_EQ(0, statistics.instance_count);
}

TEST(shared_task_test, Can_return_lvalue_reference_Address_doesnt_change)
{
    std::string value = "hello world";
    std::string* finalAddress = nullptr;

    sync_wait([&]() -> shared_task<>
        {
            auto& v = co_await [&]() -> shared_task<std::string&>
            {
                co_return value;
            }();

            finalAddress = &v;
        }());

    ASSERT_EQ(&value, finalAddress);
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
        }());

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

TEST(shared_task_test, Destroys_returned_value)
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
                auto tracker = co_await taskWithReturnValueLambda();
                instanceCountBeforeDestruction = statistics.instance_count;
            }
            instanceCountAfterDestruction = statistics.instance_count;
        }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}

TEST(shared_task_test, Destroys_thrown_exception)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> shared_task<int>
    {
        throw statistics.tracker();
        co_return 5;
    };

    sync_wait([&]() -> shared_task<>
        {
            {
                auto task = taskWithReturnValueLambda();
                try
                {
                    co_await std::move(task);
                }
                catch (lifetime_tracker&)
                {
                    instanceCountBeforeDestruction = statistics.instance_count;
                }
            }
            instanceCountAfterDestruction = statistics.instance_count;
        }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}
