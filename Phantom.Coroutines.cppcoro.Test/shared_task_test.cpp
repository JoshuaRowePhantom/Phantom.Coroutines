#include "../Phantom.Coroutines.Test/async_test.h"
#include "cppcoro/shared_task.hpp"

static_assert(std::same_as<cppcoro::shared_task<>, Phantom::Coroutines::shared_task<>>);
static_assert(std::same_as<::Phantom::Coroutines::shared_task<>, decltype(::cppcoro::make_shared_task(std::suspend_always{}))>);

namespace cppcoro
{
ASYNC_TEST(shared_task_test, make_shared_task_returns_shared_task)
{
    auto lambda = []() -> ::Phantom::Coroutines::task<std::string>
    {
        co_return "hello world";
    };

    auto task = make_shared_task(lambda());
    static_assert(std::same_as<::cppcoro::shared_task<std::string>, decltype(task)>);
    EXPECT_EQ("hello world", co_await task);
}
}
