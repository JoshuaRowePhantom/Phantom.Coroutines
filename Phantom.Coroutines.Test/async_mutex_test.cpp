#include <chrono>
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_auto_reset_event;
import Phantom.Coroutines.async_mutex;
#else
#include "Phantom.Coroutines/async_auto_reset_event.h"
#include "Phantom.Coroutines/async_mutex.h"
#endif
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "async_test.h"

namespace Phantom::Coroutines
{

using namespace std::chrono_literals;

TEST(async_mutex_test, try_lock_returns_true_for_unlocked_mutex)
{
    async_mutex<> mutex;
    auto result = mutex.try_lock();
    ASSERT_EQ(true, result);
}

TEST(async_mutex_test, try_lock_returns_false_for_locked_mutex)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_lock();
    ASSERT_EQ(true, result1);
    auto result2 = mutex.try_lock();
    ASSERT_EQ(false, result2);
}

TEST(async_mutex_test, try_lock_scoped_returns_locked_lock_for_unlocked_mutex)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    ASSERT_TRUE(result1);
}

TEST(async_mutex_test, try_lock_scoped_returns_unlocked_lock_for_locked_mutex)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    auto result2 = mutex.try_scoped_lock();
    ASSERT_FALSE(result2);
}

TEST(async_mutex_test, unlock_unlocks_scoped_lock)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    ASSERT_TRUE(result1);
    result1.unlock();
    auto result2 = mutex.try_scoped_lock();
    ASSERT_TRUE(result2);
}

TEST(async_mutex_test, destructor_unlocks_scoped_lock)
{
    async_mutex<> mutex;
    {
        auto result1 = mutex.try_scoped_lock();
    }
    auto result2 = mutex.try_scoped_lock();
    ASSERT_TRUE(result2);
}

TEST(async_mutex_test, assign_empty_unlocks_scoped_lock)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    result1 = async_mutex<>::lock_type{};
    auto result2 = mutex.try_scoped_lock();
    ASSERT_TRUE(result2);
}

TEST(async_mutex_test, assign_self_keeps_scoped_lock)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    result1 = std::move(result1);
    auto result2 = mutex.try_scoped_lock();
    ASSERT_FALSE(result2);
}

TEST(async_mutex_test, double_unlock_scoped_lock_does_not_unlock)
{
    async_mutex<> mutex;
    auto result1 = mutex.try_scoped_lock();
    result1.unlock();
    auto result2 = mutex.try_scoped_lock();
    result1.unlock();
    auto result3 = mutex.try_scoped_lock();
    ASSERT_FALSE(result3);
}

ASYNC_TEST(async_mutex_test, scoped_lock_releases_on_destruction)
{
    async_mutex<> mutex;
    async_auto_reset_event<> event;

    bool complete1 = false;
    bool complete2 = false;

    auto lambda = [&](
        bool& complete
        ) -> task<>
    {
        auto lock = co_await mutex.scoped_lock_async();
        complete = true;
        co_await event;
    };

    async_scope<> scope;
    scope.spawn(lambda(complete1));
    scope.spawn(lambda(complete2));

    EXPECT_TRUE(complete1);
    EXPECT_FALSE(complete2);
    event.set();
    EXPECT_TRUE(complete2);
    event.set();

    co_await scope.join();
}
task<> foo()
{
    async_mutex<> mutex;
    co_await mutex.lock_async();
}

ASYNC_TEST(async_mutex_test, lock_on_unlocked_mutex_acquires_mutex)
{
    async_mutex<> mutex;
    co_await mutex.lock_async();
    EXPECT_FALSE(mutex.try_lock());
}

TEST(async_mutex_test, lock_acquires_in_order)
{
    async_mutex<> mutex;
    int order = 0;

    auto acquire = [&](
        int expectedOrder
        )
    {
        return as_future([&mutex](int& order, int expectedOrder)->task<>
            {
                co_await mutex.lock_async();
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

ASYNC_TEST(async_mutex_test, noop_on_destroy_destructor_does_nothing)
{
    std::optional<async_mutex<noop_on_destroy>> mutex{std::in_place};
    co_await mutex->lock_async();

    auto future = as_future([&]() -> task<>
        {
            co_await mutex->lock_async();
            EXPECT_TRUE(false);
        });

    mutex.reset();
    EXPECT_EQ(std::future_status::timeout, future.wait_for(0s));
}

ASYNC_TEST(async_mutex_test, throw_on_destroy_destructor_causes_awaiters_to_get_exception)
{
    std::optional<async_mutex<throw_on_destroy>> mutex{ std::in_place };
    co_await mutex->lock_async();

    auto future = as_future([&]() -> task<>
        {
            co_await mutex->lock_async();
            EXPECT_TRUE(false);
        });
    mutex.reset();

    EXPECT_THROW(future.get(), std::future_error);
    co_return;
}

ASYNC_TEST(async_mutex_test, throw_on_destroy_destructor_no_awaiters_works_fine)
{
    std::optional<async_mutex<throw_on_destroy>> mutex{ std::in_place };
    co_await mutex->lock_async();
    mutex.reset();

    co_return;
}

}
