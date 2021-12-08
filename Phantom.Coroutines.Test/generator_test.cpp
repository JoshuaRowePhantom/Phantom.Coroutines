#include <gtest/gtest.h>
#include "Phantom.Coroutines/generator.h"

using namespace Phantom::Coroutines;

TEST(generator_test, Can_enumerate_empty_generator)
{
	auto myGenerator = []()->generator<int> { co_return; }();
	auto count = 0;

	for (auto& i : myGenerator)
	{
		++count;
	}

	ASSERT_EQ(0, count);
}

TEST(generator_test, Can_enumerate_non_empty_iterator)
{
	auto myGenerator = []()->generator<int> 
	{ 
		co_yield 1;
		co_yield 2;
		co_yield 3;
	}();

	auto iterator = myGenerator.begin();
	ASSERT_EQ(1, *iterator);
	ASSERT_EQ(2, *++iterator);
	ASSERT_EQ(3, *++iterator);
	ASSERT_EQ(generator<int>::iterator_type{}, ++iterator);
}

TEST(generator_test, Can_enumerate_non_empty_iterator_with_co_return)
{
	auto myGenerator = []()->generator<int>
	{
		co_yield 1;
		co_yield 2;
		co_return;
		co_yield 3;
	}();

	auto iterator = myGenerator.begin();
	ASSERT_EQ(1, *iterator);
	ASSERT_EQ(2, *++iterator);
	ASSERT_EQ(generator<int>::iterator_type{}, ++iterator);
}
