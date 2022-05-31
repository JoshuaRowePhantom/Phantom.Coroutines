#include <algorithm>
#include "async_test.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/static_thread_pool.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/thread_pool_scheduler.h"
#include <thread>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(scheduler<thread_pool_scheduler>);

ASYNC_TEST(thread_pool_scheduler_test, schedules_on_calling_process_items_thread)
{
	thread_pool_scheduler scheduler;
	async_scope scope;
	std::stop_source stopSource;
	scope.spawn([&]()->task<>
		{
			auto currentThreadId = std::this_thread::get_id();
			co_await scheduler;
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
	async_scope scope;
	scope.spawn([&]()->task<>
		{
			auto currentThreadId = std::this_thread::get_id();
			co_await scheduler;
			auto invokedThreadId = std::this_thread::get_id();
			EXPECT_NE(currentThreadId, invokedThreadId);
		}());
	sync_wait(scope.join());
}

TEST(thread_pool_scheduler_test, do_many_work_items)
{
	int numberOfItems = 1000;
	std::vector<std::thread::id> completedItems(numberOfItems);

	auto threadCount = 1ULL;
	//auto threadCount = std::thread::hardware_concurrency();
	static_thread_pool scheduler(
		threadCount
	);
	async_scope scope;

	for (size_t counter = 0; counter < numberOfItems; counter++)
	{
		scope.spawn([&](size_t counter)->task<>
			{
				co_await scheduler;
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
	ASSERT_EQ(threadCount, completedItemsByThreadId.size());
}
