#include <algorithm>
#include "async_test.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/static_thread_pool.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/thread_pool_scheduler.h"
#include "Phantom.Coroutines/sync_wait.h"
#include <barrier>
#include <thread>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(is_scheduler<thread_pool_scheduler<>>);

ASYNC_TEST(thread_pool_scheduler_test, schedules_on_calling_process_items_thread)
{
    thread_pool_scheduler<> scheduler;
    async_scope<> scope;
    std::stop_source stopSource;
    scope.spawn([&]()->task<>
        {
            auto currentThreadId = std::this_thread::get_id();
            co_await scheduler.schedule();
            auto invokedThreadId = std::this_thread::get_id();
            EXPECT_EQ(currentThreadId, invokedThreadId);
            stopSource.request_stop();
        }());
    scheduler.process_items(
        stopSource.get_token());
    co_await scope.join();
}

TEST(thread_pool_scheduler_test, schedules_on_different_thread)
{
    static_thread_pool scheduler(1);
    async_scope<> scope;
    scope.spawn([&]()->task<>
        {
            auto currentThreadId = std::this_thread::get_id();
            co_await scheduler.schedule();
            auto invokedThreadId = std::this_thread::get_id();
            EXPECT_NE(currentThreadId, invokedThreadId);
        }());
    sync_wait(scope.join());
}

ASYNC_TEST(thread_pool_scheduler_test, thread_count_is_provided_at_construction_time)
{
    static_thread_pool scheduler(4);
    EXPECT_EQ(4, scheduler.thread_count());
    co_return;
}

void thread_pool_scheduler_test_do_many_work_items_test(
    size_t numberOfItems,
    size_t numberOfThreads
)
{
    std::vector<std::thread::id> completedItems(numberOfItems);

    static_thread_pool scheduler(
        numberOfThreads
    );
    async_scope<> scope;
    std::barrier barrier(numberOfThreads);

    for (size_t counter = 0; counter < numberOfItems; counter++)
    {
        scope.spawn([&](size_t counter)->task<>
        {
            co_await scheduler.schedule();

            // The first numberOfThreads threads will wait in a blocking
            // call to ensure that all threads get used.
            if (counter < numberOfThreads)
            {
                barrier.arrive_and_wait();
            }

            EXPECT_EQ(completedItems[counter], std::thread::id{});
            completedItems[counter] = std::this_thread::get_id();
        }(counter));
    }

    sync_wait(scope.join());

    std::map<std::thread::id, size_t> completedItemsByThreadId;
    for (auto threadId : completedItems)
    {
        completedItemsByThreadId[threadId]++;
    }

    // Asserts that all items were completed.
    ASSERT_EQ(false, completedItemsByThreadId.contains(std::thread::id{}));

    // Asserts that all threads completed an item.
    ASSERT_EQ(numberOfThreads, completedItemsByThreadId.size());
}

TEST(thread_pool_scheduler_test, do_many_work_items_1_thread)
{
    thread_pool_scheduler_test_do_many_work_items_test(
        1000,
        1
    );
}

TEST(thread_pool_scheduler_test, do_many_work_items_concurrent_threads)
{
    thread_pool_scheduler_test_do_many_work_items_test(
#if NDEBUG
        1000000,
#else
        100000,
#endif
        std::thread::hardware_concurrency()
    );
}
