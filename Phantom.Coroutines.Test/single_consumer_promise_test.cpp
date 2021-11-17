#include <string>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/single_consumer_promise.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "lifetime_tracker.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;
using namespace std::string_literals;

TEST(single_consumer_promise_test, Set_after_await_causes_await_to_continue)
{
    single_consumer_promise<std::wstring> promise;
    suspend_result suspendResult;

    auto future = as_future([&]() -> task<std::wstring>
    {
        co_return co_await (suspendResult << promise);
    }());

    promise.emplace(L"hello world"s);
    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(true, suspendResult.did_suspend());
}

TEST(single_consumer_promise_test, Set_before_await_causes_await_to_not_suspend)
{
    single_consumer_promise<std::wstring> promise;
    std::optional<bool> didSuspend;
    suspend_result suspendResult;

    promise.emplace(L"hello world"s);

    auto future = as_future([&]() -> task<std::wstring>
    {
        co_return co_await (suspendResult << promise);
    }());

    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(false, suspendResult.did_suspend());
}


TEST(single_consumer_promise_test, Destroy_calls_destructor_of_embedded_value)
{
    lifetime_statistics statistics;
    {
        single_consumer_promise<lifetime_tracker> promise;

        promise.emplace(statistics.tracker());
        ASSERT_EQ(1, statistics.instance_count);
    }
    ASSERT_EQ(0, statistics.instance_count);
}
