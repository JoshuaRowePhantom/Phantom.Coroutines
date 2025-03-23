#include <gtest/gtest.h>
#include <thread>

#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.nonatomic_shared_ptr;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "lifetime_tracker.h"
#include "Phantom.Coroutines/nonatomic_shared_ptr.h"
#endif

using namespace Phantom::Coroutines;

TEST(nonatomic_shared_ptr, nonatomic_shared_ptr_starts_as_null)
{
    nonatomic_shared_ptr<lifetime_tracker> ptr;
    ASSERT_EQ(nullptr, ptr.get());
    ASSERT_EQ(nullptr, ptr.operator->());
    ASSERT_EQ(false, static_cast<bool>(ptr));
}

TEST(nonatomic_shared_ptr, nonatomic_shared_ptr_starts_as_initialized_value)
{
    lifetime_statistics statistics;
    auto tracker = new lifetime_tracker(statistics);
    nonatomic_shared_ptr<lifetime_tracker> ptr(tracker);
    ASSERT_EQ(tracker, ptr.get());
    ASSERT_EQ(tracker, ptr.operator->());
    ASSERT_EQ(tracker, &ptr.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr));
    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(1, statistics.construction_count);
}

TEST(nonatomic_shared_ptr, copy_constructor_increments_reference_count)
{
    lifetime_statistics statistics;
    auto tracker = new lifetime_tracker(statistics);
    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker);
    nonatomic_shared_ptr<lifetime_tracker> ptr2(ptr1);

    ASSERT_EQ(tracker, ptr1.get());
    ASSERT_EQ(tracker, ptr1.operator->());
    ASSERT_EQ(tracker, &ptr1.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr1));

    ASSERT_EQ(tracker, ptr2.get());
    ASSERT_EQ(tracker, ptr2.operator->());
    ASSERT_EQ(tracker, &ptr2.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr2));

    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(1, statistics.construction_count);
    ptr2.reset();
    ASSERT_EQ(1, statistics.instance_count);
    ptr1.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, move_constructor_does_not_increment_reference_count)
{
    lifetime_statistics statistics;
    auto tracker = new lifetime_tracker(statistics);
    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker);
    nonatomic_shared_ptr<lifetime_tracker> ptr2(std::move(ptr1));

    ASSERT_EQ(nullptr, ptr1.get());
    ASSERT_EQ(nullptr, ptr1.operator->());
    ASSERT_EQ(false, static_cast<bool>(ptr1));

    ASSERT_EQ(tracker, ptr2.get());
    ASSERT_EQ(tracker, ptr2.operator->());
    ASSERT_EQ(tracker, &ptr2.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr2));

    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(1, statistics.construction_count);
    ptr2.reset();
    ASSERT_EQ(0, statistics.instance_count);
    ptr1.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, copy_assignment_increments_reference_count)
{
    lifetime_statistics statistics;
    auto tracker = new lifetime_tracker(statistics);
    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker);
    nonatomic_shared_ptr<lifetime_tracker> ptr2;
    ptr2 = ptr1;

    ASSERT_EQ(tracker, ptr1.get());
    ASSERT_EQ(tracker, ptr1.operator->());
    ASSERT_EQ(tracker, &ptr1.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr1));

    ASSERT_EQ(tracker, ptr2.get());
    ASSERT_EQ(tracker, ptr2.operator->());
    ASSERT_EQ(tracker, &ptr2.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr2));

    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(1, statistics.construction_count);
    ptr2.reset();
    ASSERT_EQ(1, statistics.instance_count);
    ptr1.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, move_assignment_does_not_increment_reference_count)
{
    lifetime_statistics statistics;
    auto tracker = new lifetime_tracker(statistics);
    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker);
    nonatomic_shared_ptr<lifetime_tracker> ptr2;
    ptr2 = std::move(ptr1);

    ASSERT_EQ(nullptr, ptr1.get());
    ASSERT_EQ(nullptr, ptr1.operator->());
    ASSERT_EQ(false, static_cast<bool>(ptr1));

    ASSERT_EQ(tracker, ptr2.get());
    ASSERT_EQ(tracker, ptr2.operator->());
    ASSERT_EQ(tracker, &ptr2.operator*());
    ASSERT_EQ(true, static_cast<bool>(ptr2));

    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(1, statistics.construction_count);
    ptr2.reset();
    ASSERT_EQ(0, statistics.instance_count);
    ptr1.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, copy_assignment_decrements_reference_count)
{
    lifetime_statistics statistics1;
    auto tracker1 = new lifetime_tracker(statistics1);
    lifetime_statistics statistics2;
    auto tracker2 = new lifetime_tracker(statistics2);

    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker1);
    nonatomic_shared_ptr<lifetime_tracker> ptr2(ptr1);
    nonatomic_shared_ptr<lifetime_tracker> ptr3(tracker2);

    ASSERT_EQ(1, statistics1.instance_count);
    ptr2 = ptr3;
    ASSERT_EQ(1, statistics1.instance_count);
    ptr1 = ptr3;
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(nonatomic_shared_ptr, move_assignment_decrements_reference_count)
{
    lifetime_statistics statistics1;
    auto tracker1 = new lifetime_tracker(statistics1);
    lifetime_statistics statistics2;
    auto tracker2 = new lifetime_tracker(statistics2);

    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker1);
    nonatomic_shared_ptr<lifetime_tracker> ptr2(ptr1);
    nonatomic_shared_ptr<lifetime_tracker> ptr3(tracker2);

    ASSERT_EQ(1, statistics1.instance_count);
    ptr2 = std::move(ptr3);
    ASSERT_EQ(1, statistics1.instance_count);
    ptr1 = std::move(ptr3);
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
}

TEST(nonatomic_shared_ptr, deleter_uses_most_derived_destructor)
{
    bool deleterInvoked = false;

    struct base
    {

    };

    struct derived : base
    {
        bool* deleterInvoked;
        ~derived()
        { 
            *deleterInvoked = true;
        }
    };

    {
        nonatomic_shared_ptr<base> ptr(new derived(base(), & deleterInvoked));
    }

    ASSERT_EQ(true, deleterInvoked);
}

TEST(nonatomic_shared_ptr, swap_swaps_values_and_reference_counts)
{
    lifetime_statistics statistics1;
    auto tracker1 = new lifetime_tracker(statistics1);
    lifetime_statistics statistics2;
    auto tracker2 = new lifetime_tracker(statistics2);

    nonatomic_shared_ptr<lifetime_tracker> ptr1(tracker1);
    nonatomic_shared_ptr<lifetime_tracker> ptr2(tracker2);

    swap(ptr1, ptr2);

    ASSERT_EQ(tracker2, ptr1.get());
    ASSERT_EQ(tracker1, ptr2.get());

    ASSERT_EQ(1, statistics1.instance_count);
    ASSERT_EQ(1, statistics2.instance_count);
    ptr1.reset();
    ASSERT_EQ(1, statistics1.instance_count);
    ASSERT_EQ(0, statistics2.instance_count);
    ptr2.reset();
    ASSERT_EQ(0, statistics1.instance_count);
    ASSERT_EQ(0, statistics2.instance_count);
}

TEST(nonatomic_shared_ptr, aliasing_copy_constructor_uses_same_control_block_as_original_instance_and_adds_reference_count)
{
    lifetime_statistics statistics;
    auto value = new std::tuple<lifetime_tracker, int>(statistics, 5);
    nonatomic_shared_ptr ptr1(value);
    auto ptr2 = nonatomic_shared_ptr<int>{ ptr1, &get<1>(*ptr1) };
    ASSERT_EQ(true, static_cast<bool>(ptr1));
    ASSERT_EQ(true, static_cast<bool>(ptr2));
    ASSERT_EQ(&get<1>(*ptr1), ptr2.get());
    ASSERT_EQ(get<1>(*value), 5);
    ASSERT_EQ(*ptr2, 5);
    *ptr2 = 6;
    ASSERT_EQ(get<1>(*value), 6);
    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(*ptr2, 6);
    ptr1.reset();
    ASSERT_EQ(1, statistics.instance_count);
    ptr2.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, aliasing_move_constructor_uses_same_control_block_as_original_instance_and_does_not_add_reference_count)
{
    lifetime_statistics statistics;
    auto value = new std::tuple<lifetime_tracker, int>(statistics, 5);
    nonatomic_shared_ptr ptr1(value);
    auto ptr2 = nonatomic_shared_ptr<int>{ std::move(ptr1), &get<1>(*ptr1) };
    ASSERT_EQ(false, static_cast<bool>(ptr1));
    ASSERT_EQ(true, static_cast<bool>(ptr2));
    ASSERT_EQ(nullptr, ptr1.get());
    ASSERT_EQ(get<1>(*value), 5);
    ASSERT_EQ(*ptr2, 5);
    *ptr2 = 6;
    ASSERT_EQ(get<1>(*value), 6);
    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_EQ(*ptr2, 6);
    ASSERT_EQ(1, statistics.instance_count);
    ptr2.reset();
    ASSERT_EQ(0, statistics.instance_count);
    ptr1.reset();
    ASSERT_EQ(0, statistics.instance_count);
}

TEST(nonatomic_shared_ptr, comparison_uses_pointer_value)
{
    // Construct two aliased pointers to the same location,
    // they should compare equal even though they use different control blocks.
    nonatomic_shared_ptr ptr1 = make_nonatomic_shared<int>(1);
    nonatomic_shared_ptr ptr2 = make_nonatomic_shared<int>(2);

    int aliasValues[] = { 3, 4 };
    auto& [actualValue3, actualValue4] = aliasValues;

    nonatomic_shared_ptr ptr1_alias_3 = { ptr1, &actualValue3 };
    nonatomic_shared_ptr ptr2_alias_3 = { ptr2, &actualValue3 };
    nonatomic_shared_ptr ptr1_alias_4 = { ptr1, &actualValue4 };
    nonatomic_shared_ptr ptr2_alias_4 = { ptr2, &actualValue4 };

    ASSERT_EQ(false, ptr1 == ptr2);
    ASSERT_EQ(true, ptr1 != ptr2);
    ASSERT_EQ(true, ptr1_alias_3 == ptr2_alias_3);
    ASSERT_EQ(false, ptr1_alias_3 != ptr2_alias_3);
    ASSERT_EQ(false, ptr1_alias_3 == ptr2_alias_4);
    ASSERT_EQ(true, ptr1_alias_3 != ptr2_alias_4);

    ASSERT_EQ(true, ptr1_alias_3 < ptr2_alias_4);
}