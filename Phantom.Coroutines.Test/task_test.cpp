#include <string>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/type_traits.h"
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
