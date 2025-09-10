#include <array>
#include <iostream>
#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_mutex;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.sequence_lock;
import Phantom.Coroutines.static_thread_pool;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_mutex.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sequence_lock.h"
#include "Phantom.Coroutines/static_thread_pool.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#endif

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
                data = index + 1;
            }

            for (size_t iterationCounter = 0; iterationCounter < iterationCount; iterationCounter++)
            {
                typename sequence_lock<value>::sequence_number expectedSequenceNumber;
                auto readResult = sequenceLock.read(expectedSequenceNumber);
                EXPECT_TRUE(readResult.consistent());
                if (iterationCounter % hardwareConcurrency * 10 == 0)
                {
                    sequenceLock.write(valueToWrite);
                }
            }

            auto lock = co_await outputMutex.scoped_lock_async();
        };

        async_scope<> scope;

        for (size_t counter = 0; counter < hardwareConcurrency * 4; counter++)
        {
            scope.spawn(readerWriterLambda(counter));
        }

        co_await scope.join();
    }());
}

TEST(sequence_lock_test, read_compare_exchange_uses_sequence_number)
{
    sequence_lock<int> sequenceLock(10);
    sequence_lock<int>::sequence_number sequenceNumber;

    auto actualValue = sequenceLock.read(sequenceNumber);
    ASSERT_EQ(10, actualValue);
    ASSERT_EQ(0, sequenceNumber);

    ASSERT_TRUE(sequenceLock.compare_exchange_weak(25, sequenceNumber));
    ASSERT_EQ(4, sequenceNumber);
    actualValue = sequenceLock.read(sequenceNumber);
    ASSERT_EQ(25, actualValue);
    ASSERT_EQ(4, sequenceNumber);
}

TEST(sequence_lock_test, compare_exchange_ignores_changed_sequence_number)
{
    sequence_lock<int> sequenceLock(10);
    sequence_lock<int>::sequence_number sequenceNumber;

    auto actualValue = sequenceLock.read(sequenceNumber);
    ASSERT_EQ(10, actualValue);
    ASSERT_EQ(0, sequenceNumber);

    ASSERT_TRUE(sequenceLock.compare_exchange_weak(25, sequenceNumber));
    ASSERT_EQ(4, sequenceNumber);
    actualValue = sequenceLock.read(sequenceNumber);
    ASSERT_EQ(25, actualValue);
    ASSERT_EQ(4, sequenceNumber);

    sequenceNumber = 0;
    ASSERT_FALSE(sequenceLock.compare_exchange_weak(35, sequenceNumber));
    ASSERT_EQ(4, sequenceNumber);
    actualValue = sequenceLock.read(sequenceNumber);
    ASSERT_EQ(25, actualValue);
    ASSERT_EQ(4, sequenceNumber);
}
}