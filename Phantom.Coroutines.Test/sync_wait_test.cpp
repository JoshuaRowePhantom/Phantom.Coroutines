#include <gtest/gtest.h>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.shared_task;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/shared_task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#endif
#include "detail/awaiters.h"
#include <chrono>
#include <future>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;
using namespace std::chrono_literals;

static_assert(std::same_as<std::future<void>, decltype(as_future(typed_awaiter<void>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaiter<int>{}))>);
static_assert(std::same_as<std::future<int&>, decltype(as_future(typed_awaiter<int&>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaiter<int&&>{}))>);

static_assert(std::same_as<std::future<void>, decltype(as_future(std::declval<typed_awaiter<void>&>()))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(std::declval<typed_awaiter<int>&>()))>);
static_assert(std::same_as<std::future<int&>, decltype(as_future(std::declval<typed_awaiter<int&>&>()))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(std::declval<typed_awaiter<int&&>&>()))>);

static_assert(std::same_as<std::future<void>, decltype(as_future(std::declval<typed_awaiter<void>&&>()))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(std::declval<typed_awaiter<int>&&>()))>);
static_assert(std::same_as<std::future<int&>, decltype(as_future(std::declval<typed_awaiter<int&>&&>()))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(std::declval<typed_awaiter<int&&>&&>()))>);

static_assert(std::same_as<void, decltype(sync_wait(typed_awaiter<void>{}))>);
static_assert(std::same_as<int, decltype(sync_wait(typed_awaiter<int>{}))>);
static_assert(std::same_as<int&, decltype(sync_wait(typed_awaiter<int&>{})) > );
static_assert(std::same_as<int, decltype(sync_wait(typed_awaiter<int&&>{}))>);

static_assert(std::same_as<void, decltype(sync_wait(std::declval<typed_awaitable<void>&>()))>);
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int>&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<typed_awaitable<int&>&>())) > );
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int&&>&>()))>);

static_assert(std::same_as<void, decltype(sync_wait(std::declval<typed_awaitable<void>&&>()))>);
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int>&&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<typed_awaitable<int&>&&>())) >);
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int&&>&&>()))>);

// Verify that the lvalue/rvalue ness of the awaitable is used.
// RValue
static_assert(std::same_as<void, decltype(sync_wait(std::declval<typed_awaitable<void, void, void>>()))>);
static_assert(std::same_as<long, decltype(sync_wait(std::declval<typed_awaitable<int, void, long>>()))>);
static_assert(std::same_as<long&, decltype(sync_wait(std::declval<typed_awaitable<int&, void, long&>>())) >);
static_assert(std::same_as<long, decltype(sync_wait(std::declval<typed_awaitable<int&&, void, long&&>>()))>);

// LValue
static_assert(std::same_as<void, decltype(sync_wait(std::declval<typed_awaitable<void, void, void>&>()))>);
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int, void, long>&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<typed_awaitable<int&, void, long&>&>())) >);
static_assert(std::same_as<int, decltype(sync_wait(std::declval<typed_awaitable<int&&, void, long&&>&>()))>);

// RValue
static_assert(std::same_as<void, decltype(sync_wait(std::declval<typed_awaitable<void, void, void>&&>()))>);
static_assert(std::same_as<long, decltype(sync_wait(std::declval<typed_awaitable<int, void, long>&&>()))>);
static_assert(std::same_as<long&, decltype(sync_wait(std::declval<typed_awaitable<int&, void, long&>&&>())) >);
static_assert(std::same_as<long, decltype(sync_wait(std::declval<typed_awaitable<int&&, void, long&&>&&>()))>);


// Verify that shared_task result types get inferred correctly.
// shared_task as lvalue reference should return reference to result,
// shared_task as rvalue reference should return result.
static_assert(std::same_as<void, decltype(sync_wait(std::declval<shared_task<void>>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int>>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int&>>()))>);

static_assert(std::same_as<void, decltype(sync_wait(std::declval<shared_task<void>&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int>&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int&>&>())) >);

static_assert(std::same_as<void, decltype(sync_wait(std::declval<shared_task<void>&&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int>&&>()))>);
static_assert(std::same_as<int&, decltype(sync_wait(std::declval<shared_task<int&>&&>()))>);

TEST(as_future_test, Create_future_from_task)
{
    auto future = as_future(
        []() -> task<> { co_return; }()
    );
    future.get();
}

TEST(as_future_test, Suspends_on_event_object)
{
    async_manual_reset_event<> event;
    auto future = as_future(event);
    ASSERT_EQ(std::future_status::timeout, future.wait_for(0ms));
    event.set();
    future.get();
}

TEST(sync_wait_test, Wait_on_never_suspend)
{
    sync_wait(suspend_never{});
}

TEST(as_future_test, rethrows_exception_thrown_by_task)
{
    auto taskLambda = []() -> task<>
    {
        throw std::runtime_error("test error");
        co_return;
    };

    auto future = as_future(taskLambda());
    try
    {
        future.get();
        GTEST_FAIL();
    }
    catch (const std::runtime_error& e)
    {
        ASSERT_STREQ("test error", e.what());
    }
}

TEST(as_future_test, rethrows_exception_thrown_by_task_lambda)
{
    auto taskLambda = []() -> task<>
    {
        throw std::runtime_error("test error");
        co_return;
    };

    auto future = as_future(taskLambda);
    try
    {
        future.get();
        GTEST_FAIL();
    }
    catch (const std::runtime_error& e)
    {
        ASSERT_STREQ("test error", e.what());
    }
}

TEST(as_future_test, rethrows_exception_thrown_by_await_resume)
{
    struct awaitable : std::suspend_never
    {
        void await_resume() 
        { 
            throw std::runtime_error("test error"); 
        }
    };

    auto future = as_future(awaitable{});
    try
    {
        future.get();
        GTEST_FAIL();
    }
    catch (const std::runtime_error& e)
    {
        ASSERT_STREQ("test error", e.what());
    }
}
