#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/fibonacci_heap.h"
#include <memory>
#include <random>
#include <sstream>

using namespace Phantom::Coroutines::detail;

namespace Phantom::Coroutines
{
namespace
{

thread_local int nestedDestructorCount = 0;

struct NestedDestructorCountDecrementer
{
    ~NestedDestructorCountDecrementer()
    {
        --nestedDestructorCount;
    }
};

struct TestFibonacciHeapNode
{
    NestedDestructorCountDecrementer m_nestedDestructorCountDecrementer;
    int Key;
    size_t Degree;
    std::shared_ptr<TestFibonacciHeapNode> Child;
    std::shared_ptr<TestFibonacciHeapNode> Sibling;

    TestFibonacciHeapNode(
        int key,
        size_t degree,
        std::shared_ptr<TestFibonacciHeapNode> child = nullptr,
        std::shared_ptr<TestFibonacciHeapNode> sibling = nullptr
    )
        :
        Key(key),
        Degree(degree),
        Child(child),
        Sibling(sibling)
    {
    }

    ~TestFibonacciHeapNode()
    {
        ++nestedDestructorCount;
        assert(nestedDestructorCount < 50);
    }
};

struct TestFibonacciHeapTraits
    :
    public fibonacci_heap_builder<std::shared_ptr<TestFibonacciHeapNode>>
{
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
        }

        stream
            << "(" << heapToPrint->Key
            << "," << heapToPrint->Degree
            << "," << heapToPrint->Child
            << ")";

        heapToPrint = heapToPrint->Sibling;
        printComma = true;
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
        key,
        degree,
        child,
        next
    );
}

static_assert(is_fibonacci_heap_builder<TestFibonacciHeapTraits>);

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

bool IsCanonicalFibonacciHeap(
    const TestFibonacciHeapTraits::heap_type& heap
)
{
    TestFibonacciHeapTraits heapBuilder;
    return heapBuilder.is_canonical(heap);
}

bool IsFibonacciHeapWithNoChildren(
    const TestFibonacciHeapTraits::heap_type& heap
)
{
    for (TestFibonacciHeapTraits::heap_type root = heap;
        root;
        root = root->Sibling)
    {
        if (root->Degree != 0
            || root->Child)
        {
            return false;
        }
    }

    return true;
}

void DoFibonacciHeapTest(
    std::string expectedResultHeap,
    std::string expectedCollectedHeap,
    std::function<bool(const TestFibonacciHeapTraits::heap_type&)> predicate,
    std::initializer_list<TestFibonacciHeapTraits::heap_type> heaps
)
{
    TestFibonacciHeapTraits::heap_type collectedHeap;
    TestFibonacciHeapTraits heapBuilder;
    auto resultHeap = heapBuilder.extract(
        heapBuilder.collect_predicate(&collectedHeap, predicate),
        heaps
    );

    ASSERT_EQ(to_string(resultHeap), expectedResultHeap);
    ASSERT_EQ(to_string(collectedHeap), expectedCollectedHeap);

    ASSERT_TRUE(IsCanonicalFibonacciHeap(resultHeap));
    ASSERT_TRUE(IsFibonacciHeapWithNoChildren(collectedHeap));
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
        "[]",
        "[]",
        &AlwaysFalse,
        {
        }
    );

    DoFibonacciHeapTest(
        "[(1,0,[])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,1,[(2,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,1,[(2,0,[])]),(3,0,[])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
        }
    );


    DoFibonacciHeapTest(
        "[(1,2,[(3,1,[(4,0,[])]),(2,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,2,[(3,1,[(4,0,[])]),(2,0,[])]),(5,0,[])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,2,[(3,1,[(4,0,[])]),(2,0,[])]),(5,1,[(6,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,2,[(3,1,[(4,0,[])]),(2,0,[])]),(5,1,[(6,0,[])]),(7,0,[])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,3,[(5,2,[(7,1,[(8,0,[])]),(6,0,[])]),(3,1,[(4,0,[])]),(2,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
            MakeTestHeap(8, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,3,[(5,2,[(7,1,[(8,0,[])]),(6,0,[])]),(3,1,[(4,0,[])]),(2,0,[])]),(9,0,[])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
            MakeTestHeap(8, 0),
            MakeTestHeap(9, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,3,[(5,2,[(7,1,[(8,0,[])]),(6,0,[])]),(3,1,[(4,0,[])]),(2,0,[])]),(9,1,[(10,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
            MakeTestHeap(8, 0),
            MakeTestHeap(9, 0),
            MakeTestHeap(10, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,4,[(9,3,[(13,2,[(15,1,[(16,0,[])]),(14,0,[])]),(11,1,[(12,0,[])]),(10,0,[])]),(5,2,[(7,1,[(8,0,[])]),(6,0,[])]),(3,1,[(4,0,[])]),(2,0,[])]),(17,2,[(19,1,[(20,0,[])]),(18,0,[])])]",
        "[]",
        &AlwaysFalse,
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
            MakeTestHeap(8, 0),
            MakeTestHeap(9, 0),
            MakeTestHeap(10, 0),
            MakeTestHeap(11, 0),
            MakeTestHeap(12, 0),
            MakeTestHeap(13, 0),
            MakeTestHeap(14, 0),
            MakeTestHeap(15, 0),
            MakeTestHeap(16, 0),
            MakeTestHeap(17, 0),
            MakeTestHeap(18, 0),
            MakeTestHeap(19, 0),
            MakeTestHeap(20, 0),
        }
    );

    DoFibonacciHeapTest(
        "[(1,2,[(3,1,[(4,0,[])]),(2,0,[])])]",
        "[(20,0,[]),(19,0,[]),(18,0,[]),(17,0,[]),(16,0,[]),(15,0,[]),(14,0,[]),(13,0,[]),(12,0,[]),(11,0,[]),(10,0,[]),(9,0,[]),(8,0,[]),(7,0,[]),(6,0,[]),(5,0,[])]",
        AboveOrEqual(5),
        {
            MakeTestHeap(1, 0),
            MakeTestHeap(2, 0),
            MakeTestHeap(3, 0),
            MakeTestHeap(4, 0),
            MakeTestHeap(5, 0),
            MakeTestHeap(6, 0),
            MakeTestHeap(7, 0),
            MakeTestHeap(8, 0),
            MakeTestHeap(9, 0),
            MakeTestHeap(10, 0),
            MakeTestHeap(11, 0),
            MakeTestHeap(12, 0),
            MakeTestHeap(13, 0),
            MakeTestHeap(14, 0),
            MakeTestHeap(15, 0),
            MakeTestHeap(16, 0),
            MakeTestHeap(17, 0),
            MakeTestHeap(18, 0),
            MakeTestHeap(19, 0),
            MakeTestHeap(20, 0),
        }
    );
}

TEST(fibonacci_heap_test, big_tree_test)
{
    TestFibonacciHeapTraits heapBuilder;

    int maxValue = 100;
    int treeItems = 100000;
    int treeItemsPerBatch = 100;
    int itemsToCreatePerRemoval = 10;

    std::ranlux48 random;
    std::uniform_int_distribution<int> treeItemBatchDistribution(1, treeItemsPerBatch);
    std::uniform_int_distribution<int> valueDistribution(1, maxValue);
    std::uniform_int_distribution<int> removalBatchDistribution(0, itemsToCreatePerRemoval);

    std::vector<TestFibonacciHeapTraits::heap_type> topLevelHeaps;

    int treeItemsCreated = 0;
    
    auto createBatch = [&]()
        {
            std::vector<TestFibonacciHeapTraits::heap_type> batchHeaps;
            auto treeItemsToCreate = treeItemBatchDistribution(random);
            treeItemsCreated += treeItemsToCreate;
            for (
                ;
                treeItemsToCreate > 0;
                --treeItemsToCreate)
            {
                batchHeaps.push_back(MakeTestHeap(
                    valueDistribution(random),
                    0));
            }

            auto batchHeap = heapBuilder.extract(
                &AlwaysFalse,
                batchHeaps
            );

            EXPECT_EQ(true, IsCanonicalFibonacciHeap(batchHeap));

            return batchHeap;
        };

    while (treeItemsCreated < treeItems)
    {
        topLevelHeaps.push_back(
            createBatch());
    }

    TestFibonacciHeapTraits::heap_type topLevelHeap = heapBuilder.extract(
        &AlwaysFalse,
        topLevelHeaps
    );

    topLevelHeaps.clear();

    EXPECT_EQ(true, IsCanonicalFibonacciHeap(topLevelHeap));

    int removedItems = 0;

    for (auto removalBaseValue = 0; removalBaseValue <= maxValue; removalBaseValue++)
    {
        auto removalValue = std::uniform_int_distribution{ removalBaseValue, maxValue }(random);

        for (int removalBatchCounter = removalBatchDistribution(random);
            removalBatchCounter > 0; 
            --removalBatchCounter)
        {
            auto item = MakeTestHeap(valueDistribution(random), 0);
            item->Sibling = topLevelHeap;
            topLevelHeap = item;
            ++treeItemsCreated;
        }

        auto batch1 = createBatch();
        auto batch2 = createBatch();
        auto batch3 = createBatch();
        auto batch4 = createBatch();

        TestFibonacciHeapTraits::heap_type collectedHeap;
        topLevelHeap = heapBuilder.extract(
            heapBuilder.collect_predicate(&collectedHeap, [&](const auto& heap) -> bool { return heap->Key <= removalValue; }),
            std::array
            {
                std::move(batch1),
                std::move(batch2),
                std::move(topLevelHeap),
                std::move(batch3),
                std::move(batch4)
            }
        );

        // Verify and destroy the collected heap
        for (;
            collectedHeap;
            collectedHeap = collectedHeap->Sibling)
        {
            ++removedItems;
            EXPECT_LE(collectedHeap->Key, removalValue);
        }

        EXPECT_EQ(true, IsCanonicalFibonacciHeap(topLevelHeap));
    }
    EXPECT_EQ(true, IsCanonicalFibonacciHeap(topLevelHeap));
    EXPECT_EQ(nullptr, topLevelHeap);
    EXPECT_EQ(removedItems, treeItemsCreated);
}

}
}
