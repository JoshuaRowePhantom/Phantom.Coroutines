import "async_test.h";
import <coroutine>;
import <optional>;
import <vector>;
import Phantom.Coroutines.async_generator;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.task;
import Phantom.Coroutines.sync_wait;

namespace Phantom::Coroutines
{

static_assert(!std::is_copy_constructible_v<async_generator<int>>);
static_assert(!std::is_copy_assignable_v<async_generator<int>>);
static_assert(std::is_move_constructible_v<async_generator<int>>);
static_assert(std::is_move_assignable_v<async_generator<int>>);

ASYNC_TEST(async_generator_test, Can_enumerate_empty_async_generator)
{
	auto myGenerator = []()->async_generator<int> { co_return; }();
	auto count = 0;

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

	auto myGenerator = [&]()->async_generator<std::string>
	{
		co_yield std::move(original);
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
	}();

	auto iterator = co_await myGenerator.begin();
	EXPECT_EQ(&original, &*iterator);
}

ASYNC_TEST(async_generator_test, Moved_from_async_generator_via_construction_is_empty)
{
	std::string original;

	std::optional<async_generator<int>> myGenerator1 = [&]()->async_generator<int>
	{
		co_yield 1;
		co_yield 2;
		co_yield 3;
	}();

	auto iterator = myGenerator1->begin();
	auto myGenerator2 = std::move(*myGenerator1);

	EXPECT_EQ(co_await myGenerator1->begin(), myGenerator1->end());
}

ASYNC_TEST(async_generator_test, Moved_from_async_generator_via_assignment_is_empty)
{
	std::string original;

	std::optional<async_generator<int>> myGenerator1 = [&]()->async_generator<int>
	{
		co_yield 1;
		co_yield 2;
		co_yield 3;
	}();

	auto iterator = myGenerator1->begin();
	async_generator<int> myGenerator2;
	myGenerator2 = std::move(*myGenerator1);

	EXPECT_EQ(co_await myGenerator1->begin(), myGenerator1->end());
}
//
//ASYNC_TEST(async_generator_test, Moving_constructing_async_generator_keeps_iterators_intact)
//{
//	std::string original;
//
//	std::optional<async_generator<int>> myGenerator1 = [&]()->async_generator<int>
//	{
//		co_yield 1;
//		co_yield 2;
//		co_yield 3;
//	}();
//
//	auto iterator = co_await myGenerator1->begin();
//	EXPECT_EQ(1, *iterator);
//	EXPECT_EQ(2, *co_await ++iterator);
//
//	auto myGenerator2 = std::move(*myGenerator1);
//	myGenerator1.reset();
//	EXPECT_EQ(2, *iterator);
//	EXPECT_EQ(3, *co_await ++iterator);
//	EXPECT_EQ(myGenerator2.end(), co_await ++iterator);
//}

}