#include <gtest/gtest.h>
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "detail/awaiters.h"

using namespace Phantom::Coroutines::detail;

TEST(as_future_test, Create_future_from_task)
{
    auto future = as_future(
        []() -> task<> { co_return; }()
    );
}

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
