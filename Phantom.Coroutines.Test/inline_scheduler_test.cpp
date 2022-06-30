#include "async_test.h"
#include "Phantom.Coroutines/inline_scheduler.h"
#include <thread>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(is_scheduler<inline_scheduler>);

ASYNC_TEST(inline_scheduler_test, schedules_on_current_thread)
{
	inline_scheduler scheduler;
	auto currentThreadId = std::this_thread::get_id();
	co_await scheduler.schedule();
	auto invokedThreadId = std::this_thread::get_id();
	EXPECT_EQ(currentThreadId, invokedThreadId);
}