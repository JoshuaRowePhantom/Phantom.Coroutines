#include <gtest/gtest.h>
#include "Phantom.Coroutines/thread_local_storage.h"
#include "lifetime_tracker.h"
#include <thread>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(thread_local_storage_test, starts_with_default_value_on_multiple_threads)
{
    thread_local_storage<std::string> threadLocalStorage;
    
    std::thread thread
    {
        [&]()
        {
            ASSERT_EQ(threadLocalStorage.get(), "");
        }
    };
    thread.join();

    ASSERT_EQ(threadLocalStorage.get(), "");
}

TEST(thread_local_storage_test, starts_with_constructed_value_on_multiple_threads)
{
    thread_local_storage<std::string> threadLocalStorage{ size_t(2), 'c'};
    
    std::thread thread
    {
        [&]()
        {
            ASSERT_EQ(threadLocalStorage.get(), "cc");
        }
    };
    thread.join();

    ASSERT_EQ(threadLocalStorage.get(), "cc");
}

TEST(thread_local_storage_test, starts_with_initializer_value_on_multiple_threads)
{
    size_t invocationNumber = 0;
    thread_local_storage<std::string> threadLocalStorage{ [&]() { return std::string(++invocationNumber, 'c'); } };
    
    std::thread thread
    {
        [&]()
        {
            ASSERT_EQ(threadLocalStorage.get(), "c");
        }
    };
    thread.join();

    ASSERT_EQ(threadLocalStorage.get(), "cc");
}

namespace
{
auto& get_from_thread_local_storage(
    thread_local_storage<std::string>& storage)
{
    return storage.get();
}
}

TEST(thread_local_storage_test, new_instances_get_new_values)
{
    {
        thread_local_storage<std::string> threadLocalStorage{ "hello" };
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "hello");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "hello");
        threadLocalStorage.emplace("hello2");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "hello2");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "hello2");
    }
    {
        thread_local_storage<std::string> threadLocalStorage{ "world" };
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "world");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "world");
        threadLocalStorage.emplace("world2");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "world2");
        ASSERT_EQ(get_from_thread_local_storage(threadLocalStorage), "world2");
    }
}

