#include <gtest/gtest.h>
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_manual_reset_event;
#else
#include "Phantom.Coroutines/async_manual_reset_event.h"
#endif
#include "Phantom.Coroutines/shared_task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "detail/awaiters.h"
#include <chrono>

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