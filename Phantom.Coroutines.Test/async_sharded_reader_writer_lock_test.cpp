#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_sharded_reader_writer_lock;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_sharded_reader_writer_lock.h"
#endif

namespace Phantom::Coroutines
{

ASYNC_TEST(async_sharded_reader_writer_lock_test, can_construct)
{
    async_sharded_reader_writer_lock<> lock;
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, read_lock_blocks_write_lock_but_not_read)
{
    async_sharded_reader_writer_lock<> lock;
    auto read_lock_1 = co_await lock.reader().scoped_lock_async();
    EXPECT_EQ(true, read_lock_1.owns_lock());
    EXPECT_EQ(false, lock.writer().try_lock());
    auto read_lock2 = lock.reader().try_scoped_lock();
    EXPECT_EQ(true, read_lock2.owns_lock());
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, write_lock_blocks_read_lock)
{
    async_sharded_reader_writer_lock<> lock;
    auto write_lock_1 = co_await lock.writer().scoped_lock_async();
    auto read_lock_1 = lock.reader().try_scoped_lock();
    EXPECT_EQ(false, read_lock_1.owns_lock());
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, write_lock_blocks_write_lock)
{
    async_sharded_reader_writer_lock<> lock;
    auto write_lock_1 = co_await lock.writer().scoped_lock_async();
    auto write_lock_2 = lock.writer().try_scoped_lock();
    EXPECT_EQ(false, write_lock_2.owns_lock());
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, unlock_read_unblocks_write)
{
    async_sharded_reader_writer_lock<> lock;
    auto read_lock_1 = co_await lock.reader().scoped_lock_async();
    auto read_lock_2 = co_await lock.reader().scoped_lock_async();
    EXPECT_EQ(false, lock.writer().try_lock());
    read_lock_1.unlock();
    EXPECT_EQ(false, lock.writer().try_lock());
    read_lock_2.unlock();
    EXPECT_EQ(true, lock.writer().try_lock());
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, unlock_write_unblocks_write)
{
    async_sharded_reader_writer_lock<> lock;
    auto write_lock_1 = co_await lock.writer().scoped_lock_async();
    EXPECT_EQ(false, lock.writer().try_lock());
    write_lock_1.unlock();
    EXPECT_EQ(true, lock.writer().try_lock());
    co_return;
}

ASYNC_TEST(async_sharded_reader_writer_lock_test, unlock_write_unblocks_read)
{
    async_sharded_reader_writer_lock<> lock;
    auto write_lock_1 = co_await lock.writer().scoped_lock_async();
    auto read_lock_1 = lock.reader().try_scoped_lock();
    EXPECT_EQ(false, read_lock_1.owns_lock());
    write_lock_1.unlock();
    auto read_lock_2 = lock.reader().try_scoped_lock();
    EXPECT_EQ(true, read_lock_2.owns_lock());
    co_return;
}

}