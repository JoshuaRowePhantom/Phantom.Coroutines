#include <array>
#include <iostream>
#include "async_test.h"
#include "Phantom.Coroutines/async_mutex.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sequence_lock.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/static_thread_pool.h"

namespace Phantom::Coroutines
{
TEST(sequence_lock_test, reads_and_writes_are_consistent)
{
    static_thread_pool<> threadPool;
    sync_wait([&]() -> task<>
    {
        const size_t iterationCount = 1000000;
        const auto hardwareConcurrency = std::thread::hardware_concurrency();

        struct value
        {
            std::array<size_t, 10> m_data;
            bool consistent() const
            {
                auto expectedData = m_data[0];
                for (auto data : m_data)
                {
                    if (data != expectedData)
                    {
                        return false;
                    }
                }
                return true;
            }
        };

        sequence_lock<value> sequenceLock;
        async_mutex<> outputMutex;

        auto readerWriterLambda = [&](size_t index) -> task<>
        {
            co_await threadPool.schedule();
            value valueToWrite;
            for (auto& data : valueToWrite.m_data)
            {
                data = index;
            }

            for (size_t iterationCounter = 0; iterationCounter < iterationCount; iterationCounter++)
            {
                EXPECT_TRUE(sequenceLock.read().consistent());
                if (iterationCounter % hardwareConcurrency * 10 == 0)
                {
                    sequenceLock.write(valueToWrite);
                }
            }

            auto lock = co_await outputMutex.scoped_lock_async();
            std::cout << "Done with thread " << index << "\n";
        };

        async_scope<> scope;

        for (auto counter = 0; counter < hardwareConcurrency * 4; counter++)
        {
            scope.spawn(readerWriterLambda(counter));
        }

        co_await scope.join();
    }());
}
}