#include <gtest/gtest.h>
#include <optional>
#include <string>
#include <type_traits>
#include <vector>
#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_generator;
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.task;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_generator.h"
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"
#include "lifetime_tracker.h"
#endif

using namespace Phantom::Coroutines;

static_assert(!std::is_copy_constructible_v<async_generator<int>>);
static_assert(!std::is_copy_assignable_v<async_generator<int>>);
static_assert(std::is_move_constructible_v<async_generator<int>>);
static_assert(std::is_move_assignable_v<async_generator<int>>);

ASYNC_TEST(async_generator_test, Can_enumerate_async_generator_returning_no_elements)
{
    auto myGenerator = []()->async_generator<int>
    {
        co_return;
    }();

    for (auto iterator = co_await myGenerator.begin();
        iterator != myGenerator.end();
        co_await ++iterator)
    {
        ADD_FAILURE();
    }
}

ASYNC_TEST(async_generator_test, Can_enumerate_default_constructed_async_generator)
{
    async_generator<int> myGenerator;

    for (auto iterator = co_await myGenerator.begin();
        iterator != myGenerator.end();
        co_await ++iterator)
    {
        ADD_FAILURE();
    }
}

ASYNC_TEST(async_generator_test, Can_enumerate_non_empty_iterator)
{
    auto myGenerator = []()->async_generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_yield 3;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_EQ(1, *iterator);
    EXPECT_EQ(2, *co_await ++iterator);
    EXPECT_EQ(3, *co_await ++iterator);
    EXPECT_EQ(async_generator<int>::iterator_type{}, co_await ++iterator);
}

ASYNC_TEST(async_generator_test, Can_enumerate_non_empty_iterator_with_co_return)
{
    auto myGenerator = []()->async_generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_return;
        co_yield 3;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_EQ(1, *iterator);
    EXPECT_EQ(2, *co_await ++iterator);
    EXPECT_EQ(async_generator<int>::iterator_type{}, co_await ++iterator);
}

ASYNC_TEST(async_generator_test, Returns_reference_to_copy_for_byval_iterator_returning_lvalue)
{
    std::string original;

    auto myGenerator = [&]()->async_generator<std::string>
    {
        co_yield original;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_NE(&original, &*iterator);
}

ASYNC_TEST(async_generator_test, Returns_reference_to_original_for_byval_iterator_returning_rvalue)
{
    std::string original;

    auto myGenerator = [&]() -> async_generator<std::string>
    {
        co_yield std::move(original);
        co_return;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_EQ(&original, &*iterator);
}

ASYNC_TEST(async_generator_test, Returns_reference_to_original_for_byref_iterator_returning_lvalue)
{
    std::string original;

    auto myGenerator = [&]()->async_generator<std::string&>
    {
        co_yield original;
        co_return;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_EQ(&original, &*iterator);
}

ASYNC_TEST(async_generator_test, Returns_reference_to_original_for_byref_iterator_returning_rvalue)
{
    std::string original;

    auto myGenerator = [&]()->async_generator<std::string&>
    {
        co_yield std::move(original);
        co_return;
    }();

    auto iterator = co_await myGenerator.begin();
    EXPECT_EQ(&original, &*iterator);
}

ASYNC_TEST(async_generator_test, Can_enumerate_async_actions)
{
    async_manual_reset_event<> signal1;
    async_manual_reset_event<> signal2;

    std::vector<int> enumeratedResults;

    auto generatorLambda = [&]() -> async_generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_await signal1;
        co_yield 3;
        co_await signal2;
        co_yield 4;
    };

    auto iterationLoop = [&]() -> task<>
    {
        auto generator = generatorLambda();

        for (auto iterator = co_await generator.begin();
            iterator != generator.end();
            co_await ++iterator)
        {
            enumeratedResults.push_back(*iterator);
        }
    };

    async_scope<> scope;
    scope.spawn(iterationLoop());

    EXPECT_EQ(enumeratedResults, (std::vector<int>{ 1, 2 }));
    signal1.set();
    EXPECT_EQ(enumeratedResults, (std::vector<int>{ 1, 2, 3 }));
    signal2.set();
    EXPECT_EQ(enumeratedResults, (std::vector<int>{ 1, 2, 3, 4 }));
    co_await scope.join();
    EXPECT_EQ(enumeratedResults, (std::vector<int>{ 1, 2, 3, 4 }));
}

ASYNC_TEST(async_generator_test, Destroys_coroutine_when_not_iterated)
{
    lifetime_statistics statistics;

    auto lambda = [](auto tracker)->async_generator<std::string&>
    {
        co_return;
    };

    {
        auto myGenerator = lambda(statistics.tracker());
        EXPECT_EQ(1, statistics.instance_count);
    }
    EXPECT_EQ(0, statistics.instance_count);
    co_return;
}

ASYNC_TEST(async_generator_test, Destroys_coroutine_when_iterated_partially)
{
    lifetime_statistics statistics;

    auto lambda = [&]()->async_generator<std::string>
    {
        auto tracker = statistics.tracker();
        co_yield "hello world";
        co_yield "goodbye world";
    };

    {
        auto myGenerator = lambda();
        EXPECT_EQ(0, statistics.instance_count);
        auto iterator = co_await myGenerator.begin();
        EXPECT_EQ(1, statistics.instance_count);
        EXPECT_EQ("hello world", *iterator);
    }

    EXPECT_EQ(0, statistics.instance_count);

    {
        auto myGenerator = lambda();
        EXPECT_EQ(0, statistics.instance_count);
        auto iterator = co_await myGenerator.begin();
        EXPECT_EQ(1, statistics.instance_count);
        EXPECT_EQ("hello world", *iterator);
        myGenerator = {};
        EXPECT_EQ(0, statistics.instance_count);
    }

    co_return;
}

ASYNC_TEST(async_generator_test, Destroys_coroutine_when_iterated_completely)
{
    lifetime_statistics statistics;

    auto lambda = [&]()->async_generator<std::string>
    {
        auto tracker = statistics.tracker();
        co_yield "goodbye world";
    };

    {
        auto myGenerator = lambda();
        EXPECT_EQ(0, statistics.instance_count);
        auto iterator = co_await myGenerator.begin();
        EXPECT_EQ(1, statistics.instance_count);
        EXPECT_EQ("goodbye world", *iterator);
        co_await ++iterator;
        EXPECT_EQ(0, statistics.instance_count);
        EXPECT_EQ(iterator, myGenerator.end());
    }
}

ASYNC_TEST(async_generator_test, original_iterator_compares_equal_to_end_when_copy_incremented)
{
    auto lambda = [&]()->async_generator<std::string>
        {
            co_yield "hello";
        };

    auto generator = lambda();
    auto originalIterator = co_await generator.begin();
    auto copy = originalIterator;
    co_await ++copy;
    EXPECT_EQ(originalIterator, generator.end());
    EXPECT_EQ(copy, generator.end());
    EXPECT_EQ(originalIterator, copy);
}