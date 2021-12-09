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

TEST(async_mutex_test, try_lock_scoped_returns_locked_lock_for_unlocked_mutex)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	ASSERT_TRUE(result1);
}

TEST(async_mutex_test, try_lock_scoped_returns_unlocked_lock_for_locked_mutex)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	auto result2 = mutex.try_scoped_lock();
	ASSERT_FALSE(result2);
}

TEST(async_mutex_test, release_unlocks_scoped_lock)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	result1.release();
	auto result2 = mutex.try_scoped_lock();
	ASSERT_TRUE(result2);
}

TEST(async_mutex_test, destructor_unlocks_scoped_lock)
{
	async_mutex mutex;
	{
		auto result1 = mutex.try_scoped_lock();
	}
	auto result2 = mutex.try_scoped_lock();
	ASSERT_TRUE(result2);
}

TEST(async_mutex_test, assign_empty_unlocks_scoped_lock)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	result1 = async_mutex_lock{};
	auto result2 = mutex.try_scoped_lock();
	ASSERT_TRUE(result2);
}

TEST(async_mutex_test, assign_self_keeps_scoped_lock)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	result1 = std::move(result1);
	auto result2 = mutex.try_scoped_lock();
	ASSERT_FALSE(result2);
}

TEST(async_mutex_test, double_release_scoped_lock_does_not_unlock)
{
	async_mutex mutex;
	auto result1 = mutex.try_scoped_lock();
	result1.release();
	auto result2 = mutex.try_scoped_lock();
	result1.release();
	auto result3 = mutex.try_scoped_lock();
	ASSERT_FALSE(result3);
}

ASYNC_TEST(async_mutex_test, lock_on_unlocked_mutex_acquires_mutex)
{
	async_mutex mutex;
	co_await mutex.lock();
	EXPECT_FALSE(mutex.try_lock());
}

TEST(async_mutex_test, lock_acquires_in_order)
{
	async_mutex mutex;
	int order = 0;

	auto acquire = [&](
		int expectedOrder
		)
	{
		return as_future([&mutex](int& order, int expectedOrder)->task<>
			{
				co_await mutex.lock();
				EXPECT_EQ(order, expectedOrder);
				order = expectedOrder + 1;
			}(order, expectedOrder));
	};

	auto future0 = acquire(0);
	ASSERT_EQ(1, order);
	auto future1 = acquire(1);
	auto future2 = acquire(2);
	ASSERT_EQ(1, order);
	mutex.unlock();
	ASSERT_EQ(2, order);
	auto future3 = acquire(3);
	auto future4 = acquire(4);
	ASSERT_EQ(2, order);
	mutex.unlock();
	ASSERT_EQ(3, order);
	mutex.unlock();
	ASSERT_EQ(4, order);
	mutex.unlock();
	ASSERT_EQ(5, order);
}