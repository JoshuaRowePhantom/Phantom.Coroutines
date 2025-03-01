#include <gtest/gtest.h>
#include "async_test.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/task.h"
#include "detail/awaiters.h"

namespace Phantom::Coroutines
{
using detail::generic_awaiter;
using detail::get_unusable_task;

ASYNC_TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_true)
{
    auto testAwaiter = generic_awaiter<void, void>
    {
        .m_awaitReadyResult = true,
        .m_awaitSuspendResult = [](auto) {},
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(true, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());

    co_return;
}

ASYNC_TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_void_await_suspend)
{
    auto testAwaiter = generic_awaiter<void, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [](auto) {},
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(false, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    suspendResultAwaiter.await_suspend(coroutine_handle<>{});
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());

    co_return;
}

ASYNC_TEST(suspend_result_test, did_suspend_is_not_reset_by_second_await_when_await_ready_returns_true)
{
    auto suspendingTaskLambda = []() -> task<void>
    {
        co_return;
    };
    auto suspendingTask = suspendingTaskLambda();
    
    auto nonSuspendingAwaiter = generic_awaiter<void, void>
    {
        .m_awaitReadyResult = true,
        .m_awaitSuspendResult = [](auto) {},
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    co_await (suspendResult << std::move(suspendingTask));
    EXPECT_EQ(true, suspendResult.did_suspend());
    co_await (suspendResult << nonSuspendingAwaiter);
    EXPECT_EQ(true, suspendResult.did_suspend());
}

ASYNC_TEST(suspend_result_test, did_suspend_is_not_reset_by_second_await_when_await_suspend_returns_false)
{
    auto suspendingTaskLambda = []() -> task<void>
    {
        co_return;
    };
    auto suspendingTask = suspendingTaskLambda();
    
    auto nonSuspendingAwaiter = generic_awaiter<bool, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [](auto) { return false; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    co_await (suspendResult << std::move(suspendingTask));
    EXPECT_EQ(true, suspendResult.did_suspend());
    co_await (suspendResult << nonSuspendingAwaiter);
    EXPECT_EQ(true, suspendResult.did_suspend());
}

ASYNC_TEST(suspend_result_test, did_suspend_is_not_reset_by_second_await_when_await_suspend_returns_same_coroutine)
{
    auto suspendingTaskLambda = []() -> task<void>
    {
        co_return;
    };
    auto suspendingTask = suspendingTaskLambda();

    auto nonSuspendingAwaiter = generic_awaiter<std::coroutine_handle<>, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [](auto continuation) { return continuation; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    co_await(suspendResult << std::move(suspendingTask));
    EXPECT_EQ(true, suspendResult.did_suspend());
    co_await(suspendResult << nonSuspendingAwaiter);
    EXPECT_EQ(true, suspendResult.did_suspend());
}

ASYNC_TEST(suspend_result_test, did_suspend_is_not_reset_by_reset)
{
    auto suspendingTaskLambda = []() -> task<void>
    {
        co_return;
    };
    auto suspendingTask = suspendingTaskLambda();
    
    auto nonSuspendingAwaiter = generic_awaiter<void, void>
    {
        .m_awaitReadyResult = true,
        .m_awaitSuspendResult = [](auto) {},
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    co_await (suspendResult << std::move(suspendingTask));
    EXPECT_EQ(true, suspendResult.did_suspend());
    suspendResult.reset();
    co_await (suspendResult << nonSuspendingAwaiter);
    EXPECT_EQ(false, suspendResult.did_suspend());
}

ASYNC_TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_false_await_suspend_false)
{
    auto testAwaiter = generic_awaiter<bool, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [](auto) { return false; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(false, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(false, suspendResultAwaiter.await_suspend(coroutine_handle<>{}));
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());

    co_return;
}

ASYNC_TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_await_suspend_true)
{
    auto testAwaiter = generic_awaiter<bool, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [](auto) { return true; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(false, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(true, suspendResultAwaiter.await_suspend(coroutine_handle<>{}));
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());

    co_return;
}

ASYNC_TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_false_await_suspend_returns_same_coroutine)
{
    auto coroutine = get_unusable_task();

    auto testAwaiter = generic_awaiter<coroutine_handle<>, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [&](auto) { return coroutine.m_coroutine; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(false, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(coroutine.m_coroutine, suspendResultAwaiter.await_suspend(coroutine.m_coroutine));
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());

    co_return;
}

ASYNC_TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_await_suspend_returns_different_coroutine)
{
    auto suspendedCoroutine = get_unusable_task();
    auto transferredCoroutine = get_unusable_task();
    
    auto testAwaiter = generic_awaiter<coroutine_handle<>, void>
    {
        .m_awaitReadyResult = false,
        .m_awaitSuspendResult = [&](auto) { return transferredCoroutine.m_coroutine; },
        .m_awaitResumeResult = []() {},
    };

    suspend_result suspendResult;
    auto suspendResultAwaiter = suspendResult << testAwaiter;

    EXPECT_EQ(false, suspendResultAwaiter.await_ready());
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(transferredCoroutine.m_coroutine, suspendResultAwaiter.await_suspend(suspendedCoroutine.m_coroutine));
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(false, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());
    suspendResultAwaiter.await_resume();
    EXPECT_EQ(true, testAwaiter.m_awaitReadyCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitSuspendCalled);
    EXPECT_EQ(true, testAwaiter.m_awaitResumeCalled);
    EXPECT_EQ(true, suspendResult.did_suspend());

    co_return;
}

}