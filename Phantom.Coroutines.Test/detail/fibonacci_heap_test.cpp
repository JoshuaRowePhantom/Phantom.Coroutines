#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/fibonacci_heap.h"
#include <memory>
#include <sstream>

using namespace Phantom::Coroutines::detail;

namespace {

struct TestFibonacciHeapNode
{
	int Key;
	size_t Degree;
	std::shared_ptr<TestFibonacciHeapNode> Child;
	std::shared_ptr<TestFibonacciHeapNode> Sibling;
};

struct TestFibonacciHeapTraits
{
	typedef std::shared_ptr<TestFibonacciHeapNode> heap_type;

	static bool precedes(
		heap_type node1,
		heap_type node2
	)
	{
		return node1->Key < node2->Key;
	}

	static bool is_empty(
		heap_type node
	)
	{
		return !node;
	}

	static heap_type empty()
	{
		return heap_type{};
	}

	static heap_type* child(
		heap_type node
	)
	{
		return &node->Child;
	}

	static heap_type* sibling(
		heap_type node
	)
	{
		return &node->Sibling;
	}

	static size_t& degree(
		heap_type node
	)
	{
		return node->Degree;
	}
};

std::ostream& operator << (
	std::ostream& stream,
	const TestFibonacciHeapTraits::heap_type& heap
	)
{
	TestFibonacciHeapTraits::heap_type heapToPrint = heap;
	stream << "[";
	bool printComma = false;
	while (heapToPrint)
	{
		if (printComma)
		{
			stream << ",";
			printComma = true;
		}

		stream
			<< "(" << heapToPrint->Key
			<< "," << heapToPrint->Degree
			<< "," << heapToPrint->Child
			<< ")";

		heapToPrint = heapToPrint->Sibling;
	}
	return stream << "]";
}

std::string to_string(
	const TestFibonacciHeapTraits::heap_type& heap
)
{
	std::ostringstream stream;
	stream << heap;
	return stream.str();
}

TestFibonacciHeapTraits::heap_type MakeTestHeap()
{
	return nullptr;
}

TestFibonacciHeapTraits::heap_type MakeTestHeap(
	int key,
	size_t degree,
	TestFibonacciHeapTraits::heap_type child = nullptr,
	TestFibonacciHeapTraits::heap_type next = nullptr
)
{
	return std::make_shared<TestFibonacciHeapNode>(
		TestFibonacciHeapNode
		{
			key,
			degree,
			child,
			next
		}
	);
}

}

static_assert(FibonacciHeapTraits<TestFibonacciHeapTraits>);

TEST(fibonacci_heap_test, test_heap_equality_comparisons)
{
	TestFibonacciHeapTraits::heap_type heap1 =
		MakeTestHeap(1, 0);
	TestFibonacciHeapTraits::heap_type heap2 =
		MakeTestHeap(1, 1);
	TestFibonacciHeapTraits::heap_type heap3 =
		MakeTestHeap(1, 1, 
			MakeTestHeap(2, 2),
			MakeTestHeap(3, 2));
	TestFibonacciHeapTraits::heap_type heap4 =
		MakeTestHeap(1, 1,
			MakeTestHeap(3, 2));
	TestFibonacciHeapTraits::heap_type heap5 =
		MakeTestHeap(1, 1,
			nullptr,
			MakeTestHeap(3, 2));

	ASSERT_TRUE(to_string(heap1) == to_string(heap1));
	ASSERT_TRUE(to_string(heap2) == to_string(heap2));
	ASSERT_TRUE(to_string(heap3) == to_string(heap3));
	ASSERT_TRUE(to_string(heap4) == to_string(heap4));
	ASSERT_TRUE(to_string(heap5) == to_string(heap5));

	ASSERT_FALSE(to_string(heap2) == to_string(heap1));
	ASSERT_FALSE(to_string(heap3) == to_string(heap1));
	ASSERT_FALSE(to_string(heap4) == to_string(heap1));
	ASSERT_FALSE(to_string(heap5) == to_string(heap1));

	ASSERT_FALSE(to_string(heap1) == to_string(heap2));
	ASSERT_FALSE(to_string(heap3) == to_string(heap2));
	ASSERT_FALSE(to_string(heap4) == to_string(heap2));
	ASSERT_FALSE(to_string(heap5) == to_string(heap2));

	ASSERT_FALSE(to_string(heap1) == to_string(heap3));
	ASSERT_FALSE(to_string(heap2) == to_string(heap3));
	ASSERT_FALSE(to_string(heap4) == to_string(heap3));
	ASSERT_FALSE(to_string(heap5) == to_string(heap3));

	ASSERT_FALSE(to_string(heap1) == to_string(heap4));
	ASSERT_FALSE(to_string(heap2) == to_string(heap4));
	ASSERT_FALSE(to_string(heap3) == to_string(heap4));
	ASSERT_FALSE(to_string(heap5) == to_string(heap4));

	ASSERT_FALSE(to_string(heap1) == to_string(heap5));
	ASSERT_FALSE(to_string(heap2) == to_string(heap5));
	ASSERT_FALSE(to_string(heap3) == to_string(heap5));
	ASSERT_FALSE(to_string(heap4) == to_string(heap5));
}

namespace 
{

void DoFibonacciHeapTest(
	std::string expectedResultHeap,
	std::string expectedCollectedHeap,
	std::function<bool(const TestFibonacciHeapTraits::heap_type&)> predicate,
	std::initializer_list<TestFibonacciHeapTraits::heap_type> heaps
)
{
	TestFibonacciHeapTraits::heap_type collectedHeap;
	auto resultHeap = fibonacci_heap_extract<TestFibonacciHeapTraits>(
		fibonacci_heap_collect_predicate<TestFibonacciHeapTraits>(&collectedHeap, predicate),
		heaps
		);

	ASSERT_EQ(to_string(resultHeap), expectedResultHeap);
	ASSERT_EQ(to_string(collectedHeap), expectedCollectedHeap);
}

bool AlwaysTrue(const TestFibonacciHeapTraits::heap_type&)
{
	return true;
}

bool AlwaysFalse(const TestFibonacciHeapTraits::heap_type&)
{
	return false;
}

std::function<bool(const TestFibonacciHeapTraits::heap_type&)> AboveOrEqual(
	int value
)
{
	return [=](auto node) { return node->Key >= value; };
}

}

TEST(fibonacci_heap_test, fibonacci_heap_extract_from_empty_heap_returns_empty_heap)
{
	DoFibonacciHeapTest(
		"[]",
		"[]",
		&AlwaysFalse,
		{ nullptr }
	);
}

TEST(fibonacci_heap_test, fibonacci_heap_extract_builds_canonical_heap_from_separate_nodes)
{

	DoFibonacciHeapTest(
		"[(1,3,[(2,2,[(5,1,[(6,0,[])])(3,0,[])])(10,1,[(11,0,[])])(2,0,[])])(4,1,[(12,0,[])])]",
		"[]",
		&AlwaysFalse,
		{
			MakeTestHeap(5, 0),
			MakeTestHeap(6, 0),
			MakeTestHeap(3, 0),
			MakeTestHeap(2, 0),
			MakeTestHeap(10, 0),
			MakeTestHeap(11, 0),
			MakeTestHeap(2, 0),
			MakeTestHeap(1, 0),
			MakeTestHeap(12, 0),
			MakeTestHeap(4, 0)
		}
	);
}