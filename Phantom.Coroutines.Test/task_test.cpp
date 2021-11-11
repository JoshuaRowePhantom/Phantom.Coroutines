#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/type_traits.h"
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/sync_wait.h"

using namespace Phantom::Coroutines;

static_assert(detail::is_awaitable<task<>>);
static_assert(detail::is_awaitable<task<int>>);
static_assert(detail::is_awaitable<task<int&>>);
static_assert(detail::is_awaitable<task<int&&>>);

static_assert(std::same_as<detail::awaitable_result_type_t<task<>>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int>>, int>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>>, int&&>);

TEST(task_test, Can_await_void_task)
{
    sync_wait(
        []() -> task<>
    {
        co_return;
    }()
    );
}

TEST(task_test, Can_await_string_task)
{
    auto result = sync_wait(
        []() -> task<std::string>
    {
        co_return "hello world";
    }());

    ASSERT_EQ("hello world", result);
}

TEST(task_test, Can_return_reference)
{
    int value = 1;

    auto& result = sync_wait(
        [&]() -> task<int&>
    {
        co_return value;
    }());

    ASSERT_EQ(&value, &result);
}

TEST(task_test, Can_suspend_and_resume)
{
    single_consumer_manual_reset_event event;
    int stage = 0;

    auto future = as_future(
        [&]() -> task<>
    {
        stage = 1;
        co_await event;
        stage = 2;
    }());

    ASSERT_EQ(1, stage);
    event.set();
    ASSERT_EQ(2, stage);
}

TEST(task_test, Can_loop_without_stackoverflow)
{
    auto innerTaskLambda = []() -> task<int> { co_return 1; };
    auto outerTaskLambda = [&]() -> task<int>
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
