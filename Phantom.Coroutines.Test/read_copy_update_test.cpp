#include <gtest/gtest.h>
#include <chrono>
#include <optional>
#include <shared_mutex>

#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.Test.lifetime_tracker;
import Phantom.Coroutines.read_copy_update;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/read_copy_update.h"
#include "lifetime_tracker.h"
#endif

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(read_copy_update_test, can_read_initial_value)
{
    read_copy_update_section<std::string> section("hello world");
    ASSERT_TRUE(*section.read() == "hello world");
    ASSERT_TRUE(*section.read() == "hello world");
    ASSERT_TRUE(*section.operator->() == "hello world");
    // Verify we can call object methods via operator->
    ASSERT_EQ(section->begin(), section.read()->begin());
}

TEST(read_copy_update_test, can_read_written_const_value)
{
    read_copy_update_section<const std::string> section("hello world 1");
    section.emplace("hello world 2");
    ASSERT_EQ(*section.read(), "hello world 2");
}

TEST(read_copy_update_test, can_modify_value_before_exchange)
{
    read_copy_update_section<const std::string> section("hello world 1");
    
    auto operation = section.update();
    operation.emplace("hello world 2")[0] = '2';
    operation.exchange();
    ASSERT_EQ("2ello world 2", *operation);
    ASSERT_EQ("hello world 1", operation.original());

    ASSERT_EQ(*section.read(), "2ello world 2");
}

TEST(read_copy_update_test, can_read_modified_and_replacement_value_after_failed_exchange_and_then_succeed)
{
    read_copy_update_section<const std::string> section("hello world 1");

    auto operation1 = section.update();
    auto operation2 = section.update();

    operation1.emplace("hello world 2");
    
    ASSERT_EQ(operation1.value(), "hello world 1");

    operation2.emplace("hello world 3");
    operation2.exchange();

    ASSERT_EQ(false, operation1.compare_exchange_strong());
    // As a result of the compare_exchange_strong, operation1's current value()
    // is updated to the result of operation2.exchange()
    ASSERT_EQ(operation1.value(), "hello world 3");
    ASSERT_EQ(operation1.replacement(), "hello world 2");

    ASSERT_EQ(operation2.value(), "hello world 3");

    ASSERT_EQ(true, operation1.compare_exchange_strong());
}

TEST(read_copy_update_test, can_read_new_value_after_exchange)
{
    read_copy_update_section<const std::string> section("hello world 1");

    auto operation = section.update();
    operation.emplace("hello world 2");
    operation.exchange();

    ASSERT_EQ(operation.value(), "hello world 2");
}

TEST(read_copy_update_test, can_refresh_to_read_new_value)
{
    read_copy_update_section<const std::string> section("hello world 1");

    auto operation = section.update();
    section.emplace("hello world 2");
    ASSERT_EQ(operation.value(), "hello world 1");
    operation.refresh();
    ASSERT_EQ(operation.value(), "hello world 2");
}

TEST(read_copy_update_test, can_read_written_value)
{
    read_copy_update_section<std::string> section("hello world 1");
    section.emplace("hello world 2");
    ASSERT_EQ(*section.read(), "hello world 2");
}

TEST(read_copy_update_test, read_continues_to_return_value_at_beginning_of_read_when_replaced)
{
    read_copy_update_section<std::string> section("hello world 1");
    auto readOperation1 = section.read();
    section.emplace("hello world 2");
    ASSERT_EQ(*readOperation1, "hello world 1");
}

TEST(read_copy_update_test, write_operation_object_released_after_replace)
{
    lifetime_statistics statistics1;
    read_copy_update_section<lifetime_tracker> section{ statistics1.tracker() };

    ASSERT_EQ(1, statistics1.instance_count);
    
    lifetime_statistics statistics2;
    section.write().emplace(statistics2.tracker());

    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, write_operation_object_released_after_replace_and_last_reader_released)
{
    lifetime_statistics statistics1;
    read_copy_update_section<lifetime_tracker> section{ statistics1.tracker() };
    std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation1(section);
    std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation2(section);
    std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation3(section);

    (*readOperation1)->use();
    (*readOperation2)->use();
    (*readOperation3)->use();

    ASSERT_EQ(1, statistics1.instance_count);

    lifetime_statistics statistics2;
    section.write().emplace(statistics2.tracker());

    (*readOperation1)->use();
    (*readOperation2)->use();
    (*readOperation3)->use();

    ASSERT_EQ(1, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);

    readOperation2.reset();
    (*readOperation1)->use();
    (*readOperation3)->use();

    ASSERT_EQ(1, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);

    readOperation3.reset();
    (*readOperation1)->use();

    ASSERT_EQ(1, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);

    readOperation1.reset();

    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, object_released_after_section_destruction)
{
    lifetime_statistics statistics1;
    {
        read_copy_update_section<lifetime_tracker> section{ statistics1.tracker() };

        ASSERT_EQ(1, statistics1.instance_count);

        ASSERT_EQ(1, statistics1.instance_count);

        std::ignore = section.operator->();
    }

    ASSERT_EQ(0, statistics1.instance_count);
}

TEST(read_copy_update_test, many_parallel_uses)
{
    read_copy_update_section<std::string> section;
    std::atomic_flag finish;

    auto threadLambda = [&]()
    {
        while(!finish.test(std::memory_order_seq_cst))
        {
            for (auto counter = 0; counter < 10000; ++counter)
            {
                section.emplace("hello world");
            }
        }
    };

    std::vector<std::thread> threads;
    for (unsigned int threadCounter = 0; threadCounter < std::thread::hardware_concurrency(); threadCounter++)
    {
        threads.emplace_back(threadLambda);
    }

    std::this_thread::sleep_for(std::chrono::seconds(2));
    finish.test_and_set();
    for (auto& thread : threads)
    {
        thread.join();
    }
}

TEST(read_copy_update_test, update_operation_store_sets_value_to_new_and_sets_replacement_and_original_to_empty)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    read_copy_update_section<lifetime_tracker> section{ statistics1 };

    {
        auto updateOperation = section.update();
        updateOperation = statistics2;
        ASSERT_EQ(statistics1, *section);
        ASSERT_EQ(statistics1, *updateOperation);
        ASSERT_EQ(statistics2, updateOperation.replacement());
        updateOperation.store();

        ASSERT_EQ(statistics2, *updateOperation);

        ASSERT_EQ(statistics2, *section);
        ASSERT_EQ(0, statistics1.instance_count);
        ASSERT_EQ(1, statistics2.instance_count);
    }

    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, update_operation_exchange_set_value_to_new_and_sets_original_to_old_value)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    read_copy_update_section<lifetime_tracker> section{ statistics1 };

    {
        auto readOperation = section.read();

        {
            auto updateOperation = section.update();
            updateOperation = statistics2;
            ASSERT_EQ(statistics1, *section);
            ASSERT_EQ(statistics1, *updateOperation);
            ASSERT_EQ(statistics2, updateOperation.replacement());
            updateOperation.exchange();

            ASSERT_EQ(statistics2, *updateOperation);
            ASSERT_EQ(statistics1, updateOperation.original());

            ASSERT_EQ(statistics2, *section);
            ASSERT_EQ(1, statistics1.instance_count);
            ASSERT_EQ(1, statistics2.instance_count);
            ASSERT_EQ(&*readOperation, &updateOperation.original());
        }

        ASSERT_EQ(1, statistics1.instance_count);
        ASSERT_EQ(1, statistics2.instance_count);
    }
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, update_operation_compare_exchange_success_set_value_to_new_and_sets_original_to_old_value)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    read_copy_update_section<lifetime_tracker> section{ statistics1 };

    {
        auto readOperation = section.read();

        {
            auto updateOperation = section.update();
            updateOperation = statistics2;
            ASSERT_EQ(statistics1, *section);
            ASSERT_EQ(statistics1, *updateOperation);
            ASSERT_EQ(statistics2, updateOperation.replacement());
            bool result = updateOperation.compare_exchange_strong();
            ASSERT_EQ(true, result);

            ASSERT_EQ(statistics2, *updateOperation);
            ASSERT_EQ(statistics1, updateOperation.original());

            ASSERT_EQ(&*readOperation, &updateOperation.original());

            ASSERT_EQ(statistics2, *section);
            ASSERT_EQ(1, statistics1.instance_count);
            ASSERT_EQ(1, statistics2.instance_count);
            }

        ASSERT_EQ(1, statistics1.instance_count);
        ASSERT_EQ(1, statistics2.instance_count);
    }
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, update_operation_compare_exchange_failure_set_value_to_current_and_keeps_replacement_to_new_value)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    lifetime_statistics statistics3;
    read_copy_update_section<lifetime_tracker> section{ statistics1 };

    {
        auto updateOperation = section.update();
        updateOperation = statistics2;
        ASSERT_EQ(statistics1, *section);
        ASSERT_EQ(statistics1, *updateOperation);
        ASSERT_EQ(statistics2, updateOperation.replacement());

        section.emplace(statistics3);

        bool result = updateOperation.compare_exchange_strong();
        ASSERT_EQ(false, result);

        ASSERT_EQ(statistics3, *updateOperation);
        ASSERT_EQ(statistics2, updateOperation.replacement());

        ASSERT_EQ(statistics3, *section);
        ASSERT_EQ(0, statistics1.instance_count);
        ASSERT_EQ(1, statistics2.instance_count);
        ASSERT_EQ(1, statistics3.instance_count);
    }
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(0, statistics2.instance_count);
    ASSERT_EQ(1, statistics3.instance_count);
}

TEST(read_copy_update_test, performance_test)
{
    bool debug = false;

    std::vector<std::thread> threads;
    read_copy_update_section<std::string> section;
    std::atomic_flag flag;
    std::atomic<size_t> totalReads;

    std::function<void()> threadLambda = [&]()
    {
        size_t sectionReadCounter = 0;
        while (!flag.test())
        {
            section.read().value();
            sectionReadCounter++;
            if (sectionReadCounter % 1000000 == 0)
            {
                section.emplace("hello");
            }
        }
        totalReads += sectionReadCounter;
    };

    for (unsigned threadCounter = 0; threadCounter < (debug ? 1 : std::thread::hardware_concurrency()); ++threadCounter)
    {
        threads.emplace_back(threadLambda);
    }

    using namespace std::chrono_literals;
    std::this_thread::sleep_for(debug ? 5000s : 5s);

    flag.test_and_set();
    for (auto& thread : threads)
    {
        thread.join();
    }

    std::cerr << "Read count: " << totalReads.load() << "\n";
}

TEST(read_copy_update_test, performance_test_srw)
{
    std::vector<std::thread> threads;
    std::shared_mutex mutex;
    std::atomic_flag flag;
    std::atomic<size_t> totalReads;
    std::string value;

    std::function<void()> threadLambda = [&]()
    {
        size_t sectionReadCounter = 0;
        while (!flag.test())
        {
            {
                std::shared_lock lock{ mutex };
                sectionReadCounter++;
            }
            if (sectionReadCounter % 10000 == 0)
            {
                std::unique_lock lock{ mutex };
                value = "hello";
            }
        }
        totalReads += sectionReadCounter;
    };

    for (unsigned threadCounter = 0; threadCounter < std::thread::hardware_concurrency() /*1*/; ++threadCounter)
    //for (unsigned threadCounter = 0; threadCounter < 1; ++threadCounter)
    {
        threads.emplace_back(threadLambda);
    }

    using namespace std::chrono_literals;
    std::this_thread::sleep_for(5s);
    //std::this_thread::sleep_for(500s);

    flag.test_and_set();
    for (auto& thread : threads)
    {
        thread.join();
    }

    std::cerr << "Read count: " << totalReads.load() << "\n";
}

typedef read_copy_update_section<std::string> rcu_string;
typedef read_copy_update_section<const std::string> rcu_const_string;

extern rcu_string declval_rcu_string;
extern rcu_const_string declval_rcu_const_string;

static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.read())>);
static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.operator->())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.read())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.operator->())>);
