#include "async_test.h"
#include "Phantom.Coroutines/thread_local_contextual_promise.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.Test.lifetime_tracker;
#else
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "lifetime_tracker.h"
#endif
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines
{

namespace
{
using TestContext = thread_local_context<lifetime_tracker*>;

template<
    typename Result = void
> using TestThreadLocalContextTask = basic_task<
    thread_local_contextual_promise<
        TestContext,
        task_promise<Result>
    >
>;
}

ASYNC_TEST(thread_local_contextual_promise, sets_context_during_promise_execution)
{
    lifetime_statistics statistics;
    async_manual_reset_event<> signal;

    EXPECT_EQ(nullptr, TestContext::current());
    auto tracker = statistics.tracker();

    std::thread::id expectedThreadId;

    TestContext::current() = &tracker;
    async_scope<> scope;
    scope.spawn([&]() -> TestThreadLocalContextTask<>
    {
        EXPECT_EQ(&tracker, TestContext::current());
        co_await signal;
        EXPECT_EQ(expectedThreadId, std::this_thread::get_id());
        EXPECT_EQ(&tracker, TestContext::current());
    });

    std::thread backgroundThread([&]()
    {
        expectedThreadId = std::this_thread::get_id();
        signal.set();
        EXPECT_EQ(nullptr, TestContext::current());
    });

    co_await scope.join();
    backgroundThread.detach();
}
}