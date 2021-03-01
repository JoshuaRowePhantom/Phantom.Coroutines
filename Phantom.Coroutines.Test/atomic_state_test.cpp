#include <gtest/gtest.h>
#include "Phantom.Coroutines/atomic_state.h"

namespace Phantom::Coroutines
{
namespace
{
struct Label1 {};
struct Label2 {};

struct PointedToValue {};

struct PointedToValue1 {};
struct PointedToValue2 {};

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>
> test_atomic_state_with_singletons;

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>,
    StateSet<PointedToValue*>
> test_atomic_state_with_pointer_set;

typedef atomic_state<
    SingletonState<Label1>,
    SingletonState<Label2>,
    StateSet<PointedToValue1*>,
    StateSet<PointedToValue2*>
> test_atomic_state_with_two_sets;
}

TEST(atomic_state_test, Can_create_and_destroy_state_with_singletons)
{
    test_atomic_state_with_singletons state
    {
        Label1()
    };
}

TEST(atomic_state_test, Can_store_singleton_values)
{
    test_atomic_state_with_singletons state
    {
        Label2()
    };

    auto value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value == Label2());
    ASSERT_TRUE(value.is_singleton());

    state.store(Label1());
    value = state.load();
    ASSERT_TRUE(value == Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value.is_singleton());
}

TEST(atomic_state_test, Can_store_pointer_values_into_state_with_one_set)
{
    PointedToValue value1;
    PointedToValue value2;

    test_atomic_state_with_pointer_set state
    {
        Label1()
    };

    auto value = state.load();
    ASSERT_TRUE(value == Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1);
    ASSERT_TRUE(value != &value2);
    ASSERT_TRUE(value.is_singleton());
    ASSERT_TRUE(value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue*>());

    state.store(Label2());
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value == Label2());
    ASSERT_TRUE(value != &value1);
    ASSERT_TRUE(value != &value2);
    ASSERT_TRUE(value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue*>());

    state.store(&value1);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value == &value1);
    ASSERT_TRUE(value != &value2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(value.is<PointedToValue*>());

    state.store(&value2);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1);
    ASSERT_TRUE(value == &value2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(value.is<PointedToValue*>());
}

TEST(atomic_state_test, Can_store_pointer_values_into_state_with_two_sets)
{
    PointedToValue1 value1_1;
    PointedToValue1 value1_2;
    PointedToValue2 value2_1;
    PointedToValue2 value2_2;

    test_atomic_state_with_two_sets state
    {
        Label1()
    };

    auto value = state.load();
    ASSERT_TRUE(value == Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1_1);
    ASSERT_TRUE(value != &value1_2);
    ASSERT_TRUE(value != &value2_1);
    ASSERT_TRUE(value != &value2_2);
    ASSERT_TRUE(value.is_singleton());
    ASSERT_TRUE(value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue1*>());
    ASSERT_TRUE(!value.is<PointedToValue2*>());

    state.store(Label2());
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value == Label2());
    ASSERT_TRUE(value != &value1_1);
    ASSERT_TRUE(value != &value1_2);
    ASSERT_TRUE(value != &value2_1);
    ASSERT_TRUE(value != &value2_2);
    ASSERT_TRUE(value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue1*>());
    ASSERT_TRUE(!value.is<PointedToValue2*>());

    state.store(&value1_1);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value == &value1_1);
    ASSERT_TRUE(value != &value1_2);
    ASSERT_TRUE(value != &value2_1);
    ASSERT_TRUE(value != &value2_2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(value.is<PointedToValue1*>());
    ASSERT_TRUE(!value.is<PointedToValue2*>());

    state.store(&value1_2);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1_1);
    ASSERT_TRUE(value == &value1_2);
    ASSERT_TRUE(value != &value2_1);
    ASSERT_TRUE(value != &value2_2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(value.is<PointedToValue1*>());
    ASSERT_TRUE(!value.is<PointedToValue2*>());

    state.store(&value2_1);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1_1);
    ASSERT_TRUE(value != &value1_2);
    ASSERT_TRUE(value == &value2_1);
    ASSERT_TRUE(value != &value2_2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue1*>());
    ASSERT_TRUE(value.is<PointedToValue2*>());

    state.store(&value2_2);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1_1);
    ASSERT_TRUE(value != &value1_2);
    ASSERT_TRUE(value != &value2_1);
    ASSERT_TRUE(value == &value2_2);
    ASSERT_TRUE(!value.is_singleton());
    ASSERT_TRUE(!value.is<Label1>());
    ASSERT_TRUE(!value.is<Label2>());
    ASSERT_TRUE(!value.is<PointedToValue1*>());
    ASSERT_TRUE(value.is<PointedToValue2*>());
}


TEST(atomic_state_test, Can_retrieve_pointer_value_from_set)
{
    PointedToValue value1;

    test_atomic_state_with_pointer_set state
    {
        &value1
    };

    ASSERT_TRUE(state.load().as<PointedToValue*>() == &value1);
}

}
