#include <gtest/gtest.h>
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

using namespace Phantom::Coroutines;

TEST(as_future_test, Create_future_from_task)
{
    auto future = as_future(
        []() -> task<> { co_return; }()
    );
}