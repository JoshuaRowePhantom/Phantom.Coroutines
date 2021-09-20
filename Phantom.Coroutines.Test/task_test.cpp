#include <string>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/sync_wait.h"

using namespace Phantom::Coroutines;

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
