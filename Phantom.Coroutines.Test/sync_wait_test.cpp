#include <gtest/gtest.h>
#include "Phantom.Coroutines/single_consumer_manual_reset_event.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "detail/awaiters.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;
using namespace std::chrono_literals;

static_assert(std::same_as<std::future<void>, decltype(as_future(typed_awaiter<void>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaiter<int>{}))>);
static_assert(std::same_as<std::future<int&>, decltype(as_future(typed_awaiter<int&>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaiter<int&&>{}))>);

static_assert(std::same_as<std::future<void>, decltype(as_future(typed_awaitable<void>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaitable<int>{}))>);
static_assert(std::same_as<std::future<int&>, decltype(as_future(typed_awaitable<int&>{}))>);
static_assert(std::same_as<std::future<int>, decltype(as_future(typed_awaitable<int&&>{}))>);

static_assert(std::same_as<void, decltype(sync_wait(typed_awaiter<void>{}))>);
static_assert(std::same_as<int, decltype(sync_wait(typed_awaiter<int>{}))>);
static_assert(std::same_as<int&, decltype(sync_wait(typed_awaiter<int&>{})) > );
static_assert(std::same_as<int, decltype(sync_wait(typed_awaiter<int&&>{}))>);

static_assert(std::same_as<void, decltype(sync_wait(typed_awaitable<void>{}))>);
static_assert(std::same_as<int, decltype(sync_wait(typed_awaitable<int>{}))>);
static_assert(std::same_as<int&, decltype(sync_wait(typed_awaitable<int&>{})) > );
static_assert(std::same_as<int, decltype(sync_wait(typed_awaitable<int&&>{}))>);

static_assert(std::same_as<void, decltype(sync_wait(typed_awaitable<void>{})) > );
static_assert(std::same_as<std::string, decltype(sync_wait(typed_awaitable<std::string>{}))> );
static_assert(std::same_as<std::string&, decltype(sync_wait(typed_awaitable<std::string&>{}))> );
static_assert(std::same_as<std::string, decltype(sync_wait(typed_awaitable<std::string&&>{}))> );

TEST(as_future_test, Create_future_from_task)
{
    auto future = as_future(
        []() -> task<> { co_return; }()
    );
    future.get();
}

TEST(as_future_test, Suspends_on_event_object)
{
    single_consumer_manual_reset_event event;
    auto future = as_future(event);
    ASSERT_EQ(std::future_status::timeout, future.wait_for(0ms));
    event.set();
    future.get();
}

TEST(sync_wait_test, Wait_on_never_suspend)
{
    sync_wait(suspend_never{});
}