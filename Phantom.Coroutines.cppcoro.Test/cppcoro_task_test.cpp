#include "async_test.h"
#include <concepts>
#include "cppcoro/task.hpp"


namespace Phantom::cppcoro_test
{
using namespace ::cppcoro;
static_assert(std::same_as<task<>, decltype(make_task(std::suspend_always{})) > );

ASYNC_TEST(task_test, make_task_returns_task)
{
    auto lambda = []() -> ::cppcoro::task<std::string>
    {
        co_return "hello world";
    };

    auto task = cppcoro::make_task(lambda());
    static_assert(std::same_as<::cppcoro::task<std::string>, decltype(task)>);
    EXPECT_EQ("hello world", co_await task);
}
}
