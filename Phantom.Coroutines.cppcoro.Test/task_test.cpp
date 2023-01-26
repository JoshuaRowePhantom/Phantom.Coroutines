#include "../Phantom.Coroutines.Test/async_test.h"
#include <concepts>
#include "cppcoro/task.hpp"

static_assert(std::same_as<::Phantom::Coroutines::reusable_task<>, ::cppcoro::task<>>);
static_assert(std::same_as<::Phantom::Coroutines::reusable_task<>, decltype(::cppcoro::make_task(std::suspend_always{}))>);

namespace cppcoro
{
ASYNC_TEST(task_test, make_task_returns_task)
{
    auto lambda = []() -> ::Phantom::Coroutines::task<std::string>
    {
        co_return "hello world";
    };

    auto task = make_task(lambda());
    static_assert(std::same_as<::cppcoro::task<std::string>, decltype(task)>);
    EXPECT_EQ("hello world", co_await task);
}
}
