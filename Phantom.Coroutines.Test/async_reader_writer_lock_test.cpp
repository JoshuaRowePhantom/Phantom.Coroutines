#include "async_test.h"
#include <array>
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_reader_writer_lock.h"

namespace Phantom::Coroutines
{

ASYNC_TEST(async_reader_writer_lock_test, has_correct_reader_writer_sequencing)
{
    async_reader_writer_lock<> reader_writer_lock;

    struct operation
    {
        bool acquired = false;
        async_manual_reset_event<> signal;
        explicit operator bool() const
        {
            return acquired;
        }
    };

    auto readLambda = [&](
        operation& operation
        ) -> task<>
    {
        auto lock = co_await reader_writer_lock.reader().scoped_lock_async();
        operation.acquired = true;
        co_await operation.signal;
    };

    auto writeLambda = [&](
        operation& operation
        ) -> task<>
    {
        auto lock = co_await reader_writer_lock.writer().scoped_lock_async();
        operation.acquired = true;
        co_await operation.signal;
    };

    std::array<operation, 10> operations;
    auto expect = [&](std::vector<size_t> indices, bool complete)
    {
        for (auto index : indices)
        {
            EXPECT_EQ(operations[index].acquired, complete);
        }
    };
    auto signal = [&](size_t index)
    {
        operations[index].signal.set();
    };

    async_scope<> scope;
    scope.spawn(readLambda(operations[0]));
    expect({ 0 }, true);
    scope.spawn(readLambda(operations[1]));
    expect({ 1 }, true);
    scope.spawn(readLambda(operations[2]));
    expect({ 2 }, true);
    scope.spawn(readLambda(operations[3]));
    expect({ 3 }, true);
    scope.spawn(readLambda(operations[4]));
    expect({ 4 }, true);
    scope.spawn(writeLambda(operations[5]));
    expect({ 5 }, false);
    scope.spawn(writeLambda(operations[6]));
    expect({ 6 }, false);
    scope.spawn(readLambda(operations[7]));
    expect({ 7 }, false);
    scope.spawn(readLambda(operations[8]));
    expect({ 8 }, false);
    scope.spawn(writeLambda(operations[9]));
    expect({ 9 }, false);

    signal(0);
    expect({ 5, 6, 7, 8, 9 }, false);
    signal(1);
    expect({ 5, 6, 7, 8, 9 }, false);
    signal(2);
    expect({ 5, 6, 7, 8, 9 }, false);
    signal(3);
    expect({ 5, 6, 7, 8, 9 }, false);
    signal(4);
    expect({ 5 }, true);
    expect({ 6, 7, 8, 9 }, false);
    signal(5);
    expect({ 6 }, true);
    expect({ 7, 8, 9 }, false);
    signal(6);
    expect({ 7, 8 }, true);
    signal(7);
    expect({ 9 }, false);
    signal(8);
    expect({ 9 }, true);
    signal(9);

    co_await scope.join();
}

}