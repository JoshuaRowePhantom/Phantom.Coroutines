#include <gtest/gtest.h>
#include "Phantom.Coroutines/async_mutex.h"
#include "async_test.h"

using namespace Phantom::Coroutines;

TEST(async_mutex_test, try_lock_returns_true_for_unlocked_mutex)
{
	async_mutex mutex;
	auto result = mutex.try_lock();
	ASSERT_EQ(true, result);
}
TEST(async_mutex_test, try_lock_returns_false_for_locked_mutex)
{
	async_mutex mutex;
	auto result1 = mutex.try_lock();
	auto result2 = mutex.try_lock();
	ASSERT_EQ(false, result2);
}
