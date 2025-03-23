#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.inline_scheduler;
import Phantom.Coroutines.scheduler;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/inline_scheduler.h"
#include "Phantom.Coroutines/scheduler.h"
#endif
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