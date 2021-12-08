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