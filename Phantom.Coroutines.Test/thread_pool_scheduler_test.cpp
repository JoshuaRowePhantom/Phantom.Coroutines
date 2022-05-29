#include "async_test.h"
#include "Phantom.Coroutines/async_scope.h"
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