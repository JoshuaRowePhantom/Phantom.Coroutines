#include "async_test.h"
#include "Phantom.Coroutines/aligned_array.h"
#include <string>

namespace Phantom::Coroutines
{

TEST(aligned_array_test, array_size_0)
{
    aligned_array<int, 0, 64> array;
    EXPECT_EQ(array.empty(), true);
    EXPECT_EQ(array.size(), 0);
    EXPECT_EQ(array.max_size(), 0);
    EXPECT_EQ((aligned_array<int, 0, 64>::empty()), true);
    EXPECT_EQ((aligned_array<int, 0, 64>::size()), 0);
    EXPECT_EQ((aligned_array<int, 0, 64>::max_size()), 0);
    EXPECT_EQ(array.begin(), array.end());
    EXPECT_EQ(array.cbegin(), array.cend());
    EXPECT_EQ(array.rbegin(), array.rend());
    EXPECT_EQ(array.crbegin(), array.crend());
    EXPECT_EQ(array, array);
}

TEST(aligned_array_test, array_size_1)
{
    aligned_array<int, 1, 64> array = { 5 };
    aligned_array<int, 1, 64> array2 = { 6 };
    EXPECT_EQ(array.empty(), false);
    EXPECT_EQ(array.size(), 1);
    EXPECT_EQ(array.max_size(), 1);
    EXPECT_EQ((aligned_array<int, 1, 64>::empty()), false);
    EXPECT_EQ((aligned_array<int, 1, 64>::size()), 1);
    EXPECT_EQ((aligned_array<int, 1, 64>::max_size()), 1);
    EXPECT_EQ(array.begin() + 1, array.end());
    EXPECT_EQ(array.cbegin() + 1, array.cend());
    EXPECT_EQ(array.rbegin() + 1, array.rend());
    EXPECT_EQ(array.crbegin() + 1, array.crend());
    EXPECT_EQ(array, array);
    EXPECT_NE(array, array2);
    EXPECT_LT(array, array2);
    EXPECT_GT(array2, array);
    EXPECT_EQ(5, array[0]);
    EXPECT_EQ(6, array2[0]);
}

TEST(aligned_array_test, array_size_2)
{
    aligned_array<int, 2, 64> array = { { 5, 7 } };
    aligned_array<int, 2, 64> array2 = { { 6, 8 } };
    EXPECT_EQ(array.empty(), false);
    EXPECT_EQ(array.size(), 2);
    EXPECT_EQ(array.max_size(), 2);
    EXPECT_EQ((aligned_array<int, 2, 64>::empty()), false);
    EXPECT_EQ((aligned_array<int, 2, 64>::size()), 2);
    EXPECT_EQ((aligned_array<int, 2, 64>::max_size()), 2);
    EXPECT_EQ(array.begin() + 2, array.end());
    EXPECT_EQ(array.cbegin() + 2, array.cend());
    EXPECT_EQ(array.rbegin() + 2, array.rend());
    EXPECT_EQ(array.crbegin() + 2, array.crend());
    EXPECT_EQ(array, array);
    EXPECT_NE(array, array2);
    EXPECT_LT(array, array2);
    EXPECT_GT(array2, array);
    EXPECT_EQ(5, array[0]);
    EXPECT_EQ(6, array2[0]);
    EXPECT_EQ(7, array[1]);
    EXPECT_EQ(8, array2[1]);
}

TEST(aligned_array_test, array_size_2_complex_construction)
{
    aligned_array<std::string, 2, 64> array = { { std::string("hello"), "world" } };
    aligned_array<std::string, 2, 64> array2 = { { { "hello" } } };
    EXPECT_EQ(array.empty(), false);
    EXPECT_EQ(array.size(), 2);
    EXPECT_EQ(array.max_size(), 2);
    EXPECT_EQ((aligned_array<int, 2, 64>::empty()), false);
    EXPECT_EQ((aligned_array<int, 2, 64>::size()), 2);
    EXPECT_EQ((aligned_array<int, 2, 64>::max_size()), 2);
    EXPECT_EQ(array.begin() + 2, array.end());
    EXPECT_EQ(array.cbegin() + 2, array.cend());
    EXPECT_EQ(array.rbegin() + 2, array.rend());
    EXPECT_EQ(array.crbegin() + 2, array.crend());
    EXPECT_EQ(array, array);
    EXPECT_NE(array, array2);
    EXPECT_GT(array, array2);
    EXPECT_LT(array2, array);
    EXPECT_EQ("hello", array[0]);
    EXPECT_EQ("hello", array2[0]);
    EXPECT_EQ("world", array[1]);
    EXPECT_EQ("", array2[1]);
}

TEST(aligned_array_test, is_actually_aligned)
{
    aligned_array<int, 3, 64> array;
    auto first = reinterpret_cast<char*>(&*array.begin());
    auto second = reinterpret_cast<char*>(&*(array.begin() + 1));
    auto third = reinterpret_cast<char*>(&array[2]);
    EXPECT_EQ(64, second - first);
    EXPECT_EQ(128, third - first);
}

TEST(aligned_array_test, test_iterator_operations)
{
    aligned_array<int, 3, 64> array{ {5, 6, 7} };

    auto first = array.begin();
    auto second = array.begin() + 1;
    auto third = second + 1;

    auto second_2 = first;
    EXPECT_EQ(first, second_2++);
    EXPECT_EQ(second_2, second);

    auto second_3 = first;
    EXPECT_EQ(second, ++second_3);
    EXPECT_EQ(second_3, second);
    
    auto second_4 = third;
    EXPECT_EQ(third, second_4--);
    EXPECT_EQ(second_2, second);

    auto second_5 = third;
    EXPECT_EQ(second, --second_5);
    EXPECT_EQ(second_5, second);

    auto third_2 = first;
    EXPECT_EQ(&third_2, &(third_2 += 2));
    EXPECT_EQ(third_2, third);
    
    auto first_2 = third;
    EXPECT_EQ(&first_2, &(first_2 -= 2));
    EXPECT_EQ(first_2, first);

    EXPECT_EQ(&array[0], &*first);
    EXPECT_EQ(&array[1], &*second);
    EXPECT_EQ(&array[2], &*third);
    EXPECT_EQ(5, *first);
    EXPECT_EQ(6, *second);
    EXPECT_EQ(7, *third);

    EXPECT_EQ(&array[0], &*array.begin());
    EXPECT_EQ(&array[0], &*array.cbegin());
    EXPECT_EQ(&array[2], &*array.rbegin());
    EXPECT_EQ(&array[2], &*array.crbegin());

    EXPECT_EQ(&array[0], &*(array.end() - 3));
    EXPECT_EQ(&array[0], &*(array.cend() - 3));
    EXPECT_EQ(&array[2], &*(array.rend() - 3));
    EXPECT_EQ(&array[2], &*(array.crend() - 3));
}

}