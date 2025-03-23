#include "async_test.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/sync_wait.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_promise;
import Phantom.Coroutines.suspend_result;
import Phantom.Coroutines.Test.lifetime_tracker;
#else
#include "Phantom.Coroutines/async_promise.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "lifetime_tracker.h"
#endif
#include <string>

namespace Phantom::Coroutines
{

using namespace std::string_literals;

TEST(async_promise_test, Set_after_await_causes_await_to_continue)
{
    async_promise<std::wstring> promise;
    suspend_result suspendResult;

    auto future = as_future([&]() -> task<std::wstring>
    {
        co_return co_await(suspendResult << promise);
    }());

    promise.emplace(L"hello world"s);
    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(true, suspendResult.did_suspend());
}

TEST(async_promise_test, Set_before_await_causes_await_to_not_suspend)
{
    async_promise<std::wstring> promise;
    std::optional<bool> didSuspend;
    suspend_result suspendResult;

    promise.emplace(L"hello world"s);

    auto future = as_future([&]() -> task<std::wstring>
    {
        co_return co_await(suspendResult << promise);
    }());

    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(false, suspendResult.did_suspend());
}


TEST(async_promise_test, Destroy_calls_destructor_of_embedded_value)
{
    lifetime_statistics statistics;
    {
        async_promise<lifetime_tracker> promise;

        promise.emplace(statistics.tracker());
        ASSERT_EQ(1, statistics.instance_count);
    }
    ASSERT_EQ(0, statistics.instance_count);
}

}
