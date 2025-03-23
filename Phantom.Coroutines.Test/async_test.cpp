#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.static_thread_pool;
import Phantom.Coroutines.sync_wait;
#else
#include "Phantom.Coroutines/static_thread_pool.h"
#include "Phantom.Coroutines/sync_wait.h"
#endif

namespace Phantom::Coroutines::Test
{
void ExecuteTest(
    ::Phantom::Coroutines::reusable_task<> testTask)
{
    // Create a thread pool to ensure that if the test itself does any threading, we
    // return control back to this thread pool.
    ::Phantom::Coroutines::static_thread_pool threadPool(1);

    auto runTestBody = [&]() -> Phantom::Coroutines::reusable_task<>
    {
        co_await testTask.when_ready();
        co_await threadPool.schedule();
        co_await testTask;
    };

    ::Phantom::Coroutines::sync_wait(runTestBody());
}

}