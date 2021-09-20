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