#include "async_test.h"
#include "Phantom.Coroutines/direct_initialized_optional.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.Test.lifetime_tracker;
#else
#include "lifetime_tracker.h"
#endif

namespace Phantom::Coroutines
{

ASYNC_TEST(direct_initialized_optional_test, default_constructed_optional_is_empty)
{
    direct_initialized_optional<lifetime_tracker> optional;
    EXPECT_FALSE(optional.has_value());
    EXPECT_FALSE(optional);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, constructed_from_invocable_does_not_move_or_copy)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional{ [&] {return statistics.tracker(); } };
    EXPECT_TRUE(optional.has_value());
    EXPECT_EQ(0, statistics.copy_count);
    EXPECT_EQ(0, statistics.destruction_count);
    EXPECT_EQ(0, statistics.move_into_count);
    EXPECT_EQ(0, statistics.move_from_count);
    EXPECT_EQ(0, statistics.move_construction_count);
    EXPECT_TRUE(optional);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, destroyed_by_reset)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional{ [&] {return statistics.tracker(); } };
    EXPECT_TRUE(optional.has_value());
    EXPECT_EQ(0, statistics.destruction_count);
    optional.reset();
    EXPECT_EQ(1, statistics.destruction_count);
    EXPECT_FALSE(optional);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, destroyed_by_destructor)
{
    lifetime_statistics statistics;
    {
        direct_initialized_optional<lifetime_tracker> optional{ [&] {return statistics.tracker(); } };
        EXPECT_TRUE(optional.has_value());
        EXPECT_EQ(0, statistics.destruction_count);
    }
    EXPECT_EQ(1, statistics.destruction_count);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_construct_empty_from_const_lvalue)
{
    lifetime_statistics statistics;
    const direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2{ optional1 };
    EXPECT_EQ(false, optional1.has_value());
    EXPECT_EQ(false, optional2.has_value());
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_construct_empty_from_lvalue)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2{ optional1 };
    EXPECT_EQ(false, optional1.has_value());
    EXPECT_EQ(false, optional2.has_value());
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_construct_empty)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2{ std::move(optional1) };
    EXPECT_EQ(false, optional1.has_value());
    EXPECT_EQ(false, optional2.has_value());
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_construct_value_from_const_lvalue)
{
    lifetime_statistics statistics;
    const direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics.tracker(); } };
    EXPECT_EQ(1, statistics.instance_count);
    direct_initialized_optional<lifetime_tracker> optional2{ optional1 };
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(2, statistics.instance_count);
    EXPECT_EQ(1, statistics.copy_construction_count);
    EXPECT_EQ(0, statistics.move_construction_count);
    EXPECT_EQ(0, statistics.copy_count);
    EXPECT_EQ(0, statistics.move_from_count);
    EXPECT_EQ(0, statistics.move_into_count);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_construct_value_from_lvalue)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics.tracker(); } };
    EXPECT_EQ(1, statistics.instance_count);
    direct_initialized_optional<lifetime_tracker> optional2{ optional1 };
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(2, statistics.instance_count);
    EXPECT_EQ(1, statistics.copy_construction_count);
    EXPECT_EQ(0, statistics.move_construction_count);
    EXPECT_EQ(0, statistics.copy_count);
    EXPECT_EQ(0, statistics.move_from_count);
    EXPECT_EQ(0, statistics.move_into_count);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_construct_value)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics.tracker(); } };
    EXPECT_EQ(1, statistics.instance_count);
    direct_initialized_optional<lifetime_tracker> optional2{ std::move(optional1) };
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(2, statistics.instance_count);
    EXPECT_EQ(0, statistics.copy_construction_count);
    EXPECT_EQ(1, statistics.move_construction_count);
    EXPECT_EQ(0, statistics.copy_count);
    EXPECT_EQ(0, statistics.move_from_count);
    EXPECT_EQ(0, statistics.move_into_count);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_assign_empty_to_empty)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2;
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    optional2 = optional1;
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_assign_empty_to_empty)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2;
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    optional2 = std::move(optional1);
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_assign_value_to_empty)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics.tracker(); } };
    direct_initialized_optional<lifetime_tracker> optional2;
    EXPECT_TRUE(optional1);
    EXPECT_FALSE(optional2);
    EXPECT_EQ(1, statistics.instance_count);
    optional2 = optional1;
    EXPECT_EQ(1, statistics.copy_construction_count);
    EXPECT_EQ(0, statistics.copy_count);
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_assign_value_to_empty)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics.tracker(); } };
    direct_initialized_optional<lifetime_tracker> optional2;
    EXPECT_TRUE(optional1);
    EXPECT_FALSE(optional2);
    EXPECT_EQ(1, statistics.instance_count);
    optional2 = std::move(optional1);
    EXPECT_EQ(1, statistics.move_construction_count);
    EXPECT_EQ(0, statistics.move_from_count);
    EXPECT_EQ(0, statistics.move_into_count);
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_assign_empty_to_value)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2{ [&] {return statistics.tracker(); } };
    EXPECT_FALSE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(1, statistics.instance_count);
    optional2 = optional1;
    EXPECT_EQ(0, statistics.instance_count);
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_assign_empty_to_value)
{
    lifetime_statistics statistics;
    direct_initialized_optional<lifetime_tracker> optional1;
    direct_initialized_optional<lifetime_tracker> optional2{ [&] {return statistics.tracker(); } };
    EXPECT_FALSE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(1, statistics.instance_count);
    optional2 = std::move(optional1);
    EXPECT_EQ(0, statistics.move_construction_count);
    EXPECT_FALSE(optional1);
    EXPECT_FALSE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_copy_assign_value_to_value)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics1.tracker(); } };
    direct_initialized_optional<lifetime_tracker> optional2{ [&] {return statistics2.tracker(); } };
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(1, statistics1.instance_count);
    EXPECT_EQ(1, statistics2.instance_count);
    optional2 = optional1;
    EXPECT_EQ(2, statistics1.instance_count);
    EXPECT_EQ(0, statistics2.instance_count);
    EXPECT_EQ(1, statistics1.copy_count);
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    co_return;
}

ASYNC_TEST(direct_initialized_optional_test, can_move_assign_value_to_value)
{
    lifetime_statistics statistics1;
    lifetime_statistics statistics2;
    direct_initialized_optional<lifetime_tracker> optional1{ [&] {return statistics1.tracker(); } };
    direct_initialized_optional<lifetime_tracker> optional2{ [&] {return statistics2.tracker(); } };
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    EXPECT_EQ(1, statistics1.instance_count);
    EXPECT_EQ(1, statistics2.instance_count);
    optional2 = std::move(optional1);
    EXPECT_EQ(2, statistics1.instance_count);
    EXPECT_EQ(0, statistics2.instance_count);
    EXPECT_EQ(1, statistics1.move_from_count);
    EXPECT_EQ(1, statistics2.move_into_count);
    EXPECT_TRUE(optional1);
    EXPECT_TRUE(optional2);
    co_return;
}

}