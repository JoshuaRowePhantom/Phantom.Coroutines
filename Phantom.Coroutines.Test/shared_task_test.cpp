#include <gtest/gtest.h>
#include "Phantom.Coroutines/shared_task.h"

using namespace Phantom::Coroutines;

TEST(shared_task_test, Can_create_default_constructed_task)
{
    shared_task<void> task;
}
