#include <gtest/gtest.h>
#include <coroutine>
#include <optional>
#include <string>
#include <vector>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.generator;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/generator.h"
#include "lifetime_tracker.h"
#endif

namespace Phantom::Coroutines
{
static_assert(!std::is_copy_constructible_v<generator<int>>);
static_assert(!std::is_copy_assignable_v<generator<int>>);
static_assert(std::is_move_constructible_v<generator<int>>);
static_assert(std::is_move_assignable_v<generator<int>>);

TEST(generator_test, Can_enumerate_empty_generator)
{
    auto myGeneratorLambda = []()->generator<int> { co_return; };
    auto myGenerator = myGeneratorLambda();
    auto count = 0;

    for (auto& i : myGenerator)
    {
        std::ignore = i;
        ++count;
    }

    ASSERT_EQ(0, count);
}

TEST(generator_test, Destroys_promise_when_partially_iterated)
{
    lifetime_statistics statistics;

    auto myGeneratorLambda = [&]()->generator<int>
    {
        auto tracker = statistics.tracker();
        co_yield 1;
    };
    
    {
        auto myGenerator = myGeneratorLambda();
        ASSERT_EQ(1, statistics.instance_count);
    }
    ASSERT_EQ(0, statistics.instance_count);

    {
        auto myGenerator = myGeneratorLambda();
        ASSERT_EQ(1, statistics.instance_count);
        myGenerator = {};
        ASSERT_EQ(0, statistics.instance_count);
    }
}

TEST(generator_test, Can_enumerate_non_empty_iterator)
{
    auto myGeneratorLambda = []()->generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_yield 3;
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_EQ(1, *iterator);
    ASSERT_EQ(2, *++iterator);
    ASSERT_EQ(3, *++iterator);
    ASSERT_EQ(generator<int>::iterator_type{}, ++iterator);
}

TEST(generator_test, Can_enumerate_non_empty_iterator_with_co_return)
{
    auto myGeneratorLambda = []()->generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_return;
        co_yield 3;
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_EQ(1, *iterator);
    ASSERT_EQ(2, *++iterator);
    ASSERT_EQ(generator<int>::iterator_type{}, ++iterator);
}

TEST(generator_test, Returns_reference_to_copy_for_byval_iterator_returning_lvalue)
{
    std::string original;

    auto myGeneratorLambda = [&]()->generator<std::string>
    {
        co_yield original;
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_NE(&original, &*iterator);
}

TEST(generator_test, Returns_reference_to_original_for_byval_iterator_returning_rvalue)
{
    std::string original;

    auto myGeneratorLambda = [&]()->generator<std::string>
    {
        co_yield std::move(original);
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_EQ(&original, &*iterator);
}

TEST(generator_test, Returns_reference_to_original_for_byref_iterator_returning_lvalue)
{
    std::string original;

    auto myGeneratorLambda = [&]()->generator<std::string&>
    {
        co_yield original;
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_EQ(&original, &*iterator);
}

TEST(generator_test, Returns_reference_to_original_for_byref_iterator_returning_rvalue)
{
    std::string original;

    auto myGeneratorLambda = [&]()->generator<std::string&>
    {
        co_yield std::move(original);
    };
    auto myGenerator = myGeneratorLambda();

    auto iterator = myGenerator.begin();
    ASSERT_EQ(&original, &*iterator);
}

TEST(generator_test, Moved_from_generator_via_construction_is_empty)
{
    std::string original;

    auto myGenerator1Lambda = [&]()->generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_yield 3;
    };
    std::optional<generator<int>> myGenerator1 = myGenerator1Lambda();

    auto iterator = myGenerator1->begin();
    auto myGenerator2 = std::move(*myGenerator1);

    auto result = std::vector<int>
    {
        myGenerator1->begin(),
        myGenerator1->end()
    };

    ASSERT_EQ(
        std::vector<int>{},
        result
    );
}

TEST(generator_test, Moved_from_generator_via_assignment_is_empty)
{
    std::string original;

    auto myGenerator1Lambda = [&]()->generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_yield 3;
    };
    std::optional<generator<int>> myGenerator1 = myGenerator1Lambda();

    auto iterator = myGenerator1->begin();
    generator<int> myGenerator2;
    myGenerator2 = std::move(*myGenerator1);

    auto result = std::vector<int>
    {
        myGenerator1->begin(),
        myGenerator1->end()
    };

    ASSERT_EQ(
        std::vector<int>{},
        result
    );
}

TEST(generator_test, Moving_constructing_generator_keeps_iterators_intact)
{
    std::string original;

    auto myGenerator1Lambda = [&]()->generator<int>
    {
        co_yield 1;
        co_yield 2;
        co_yield 3;
    };
    std::optional<generator<int>> myGenerator1 = myGenerator1Lambda();

    auto iterator = myGenerator1->begin();
    ASSERT_EQ(1, *iterator);
    ASSERT_EQ(2, *++iterator);

    auto myGenerator2 = std::move(*myGenerator1);
    myGenerator1.reset();
    ASSERT_EQ(2, *iterator);
    ASSERT_EQ(3, *++iterator);
    ASSERT_EQ(myGenerator2.end(), ++iterator);
}
}
