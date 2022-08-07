#include <gtest/gtest.h>
#include "Phantom.Coroutines/suspend_result.h"
#include "detail/awaiters.h"

namespace Phantom::Coroutines
{
using detail::generic_awaiter;
using detail::get_unusable_task;

TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_true)
{
	auto testAwaiter = generic_awaiter<void, void>
	{
		.m_awaitReadyResult = true,
		.m_awaitSuspendResult = [](auto) {},
		.m_awaitResumeResult = []() {},
	};

	suspend_result suspendResult;
	auto suspendResultAwaiter = suspendResult << testAwaiter;

	ASSERT_EQ(true, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
}

TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_void_await_suspend)
{
	auto testAwaiter = generic_awaiter<void, void>
	{
		.m_awaitReadyResult = false,
		.m_awaitSuspendResult = [](auto) {},
		.m_awaitResumeResult = []() {},
	};

	suspend_result suspendResult;
	auto suspendResultAwaiter = suspendResult << testAwaiter;

	ASSERT_EQ(false, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	suspendResultAwaiter.await_suspend(coroutine_handle<>{});
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
}

TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_false_await_suspend_false)
{
	auto testAwaiter = generic_awaiter<bool, void>
	{
		.m_awaitReadyResult = false,
		.m_awaitSuspendResult = [](auto) { return false; },
		.m_awaitResumeResult = []() {},
	};

	suspend_result suspendResult;
	auto suspendResultAwaiter = suspendResult << testAwaiter;

	ASSERT_EQ(false, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	ASSERT_EQ(false, suspendResultAwaiter.await_suspend(coroutine_handle<>{}));
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
}

TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_await_suspend_true)
{
	auto testAwaiter = generic_awaiter<bool, void>
	{
		.m_awaitReadyResult = false,
		.m_awaitSuspendResult = [](auto) { return true; },
		.m_awaitResumeResult = []() {},
	};

	suspend_result suspendResult;
	auto suspendResultAwaiter = suspendResult << testAwaiter;

	ASSERT_EQ(false, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	ASSERT_EQ(true, suspendResultAwaiter.await_suspend(coroutine_handle<>{}));
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
}

TEST(suspend_result_test, reports_not_suspended_for_await_ready_is_false_await_suspend_returns_same_coroutine)
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

	ASSERT_EQ(false, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	ASSERT_EQ(coroutine.m_coroutine, suspendResultAwaiter.await_suspend(coroutine.m_coroutine));
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
}

TEST(suspend_result_test, reports_suspended_for_await_ready_is_false_await_suspend_returns_different_coroutine)
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

	ASSERT_EQ(false, suspendResultAwaiter.await_ready());
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(false, suspendResult.did_suspend());
	ASSERT_EQ(transferredCoroutine.m_coroutine, suspendResultAwaiter.await_suspend(suspendedCoroutine.m_coroutine));
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(false, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
	suspendResultAwaiter.await_resume();
	ASSERT_EQ(true, testAwaiter.m_awaitReadyCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitSuspendCalled);
	ASSERT_EQ(true, testAwaiter.m_awaitResumeCalled);
	ASSERT_EQ(true, suspendResult.did_suspend());
}

}