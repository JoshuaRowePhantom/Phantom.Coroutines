#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.make_task;
import Phantom.Coroutines.shared_task;
#else
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/make_task.h"
#include "Phantom.Coroutines/shared_task.h"
#endif
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines
{

ASYNC_TEST(make_task, Can_make_task_returning_void)
{
    async_manual_reset_event<> event;
    auto result = make_task(event);

    static_assert(std::same_as<task<>, decltype(result)>);

    event.set();
    co_await std::move(result);
}

ASYNC_TEST(make_task, Can_make_shared_task_returning_void)
{
    async_manual_reset_event<> event;
    auto result = make_task<shared_task>(event);

    static_assert(std::same_as<shared_task<>, decltype(result)>);

    event.set();
    co_await result;
}

ASYNC_TEST(make_task, Can_make_shared_task_from_task)
{
    async_manual_reset_event<> event;
    auto lambda = [&]() -> task<>
    {
        co_return;
    };
    auto result = make_task<shared_task>(lambda());

    static_assert(std::same_as<shared_task<>, decltype(result)>);

    event.set();
    co_await result;
}

ASYNC_TEST(make_task, Can_make_shared_task_from_task_return_value)
{
    auto lambda = [&]() -> task<std::string>
    {
        co_return "hello world";
    };
    auto result = make_task<shared_task>(lambda());

    static_assert(std::same_as<shared_task<std::string>, decltype(result)>);

    EXPECT_EQ("hello world", co_await result);
}

}