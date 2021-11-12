#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/type_traits.h"
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "lifetime_tracker.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

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

TEST(task_test, Can_return_rvalue_reference_Address_doesnt_change)
{
    std::string value = "hello world";
    std::string* finalAddress;

    sync_wait([&]() -> task<>
    {
        auto& v = reinterpret_cast<std::string&>(co_await[&]() -> task<std::string&&>
        {
            co_return value;
        }());

        finalAddress = &v;
    }());

    ASSERT_EQ(&value, finalAddress);
}

TEST(task_test, Can_use_returned_rvalue_reference)
{
    detail::lifetime_statistics statistics;
    detail::lifetime_tracker initialValue = statistics.tracker();

    sync_wait([&]() -> task<>
    {
        auto endValue = co_await[&]() -> task<detail::lifetime_tracker&&>
        {
            co_return initialValue;
        }();

        [&]() {
            ASSERT_EQ(2, statistics.instance_count);
            ASSERT_EQ(1, statistics.move_construction_count);
        }();
    }());

    ASSERT_TRUE(initialValue.moved_from());
    ASSERT_EQ(1, statistics.instance_count);
}

TEST(task_test, Can_use_returned_rvalue_reference_with_same_address)
{
    detail::lifetime_statistics statistics;
    detail::lifetime_tracker initialValue = statistics.tracker();

    sync_wait([&]() -> task<>
    {
        [&](detail::lifetime_tracker&& endValue) {

            endValue.use();
            ASSERT_EQ(1, statistics.instance_count);
            ASSERT_EQ(0, statistics.move_construction_count);
        }(
            co_await[&]() -> task<detail::lifetime_tracker&&>
        {
            co_return initialValue;
        }());
    }());

    ASSERT_FALSE(initialValue.moved_from());
    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_FALSE(statistics.used_after_move);
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

TEST(task_test, Destroys_returned_value)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    sync_wait([&]() -> task<>
    {
        {
            auto task = taskWithReturnValueLambda();
            co_await task;
            instanceCountBeforeDestruction = statistics.instance_count;
        }
        instanceCountAfterDestruction = statistics.instance_count;
    }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}
