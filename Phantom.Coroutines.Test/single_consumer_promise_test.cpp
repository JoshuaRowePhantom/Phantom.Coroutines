#include <string>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/resume_result.h"
#include "Phantom.Coroutines/single_consumer_promise.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;
using namespace std::string_literals;

TEST(single_consumer_promise_test, Set_after_await_causes_await_to_continue)
{
    single_consumer_promise<std::wstring> promise;
    std::optional<bool> didSuspend;

    auto future = as_future([&]() -> task<std::wstring>
    {
        auto resumeResult = co_await with_resume_result(
            promise);
        didSuspend = resumeResult.did_suspend();
        co_return resumeResult.result();
    }());

    promise.emplace(L"hello world"s);
    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(true, didSuspend);
}


TEST(single_consumer_promise_test, Set_before_await_causes_await_to_not_suspend)
{
    single_consumer_promise<std::wstring> promise;
    std::optional<bool> didSuspend;

    promise.emplace(L"hello world"s);

    auto future = as_future([&]() -> task<std::wstring>
    {
        auto resumeResult = co_await with_resume_result(
            promise);
        didSuspend = resumeResult.did_suspend();
        co_return resumeResult.result();
    }());

    ASSERT_EQ(future.get(), L"hello world"s);
    ASSERT_EQ(false, didSuspend);
}

