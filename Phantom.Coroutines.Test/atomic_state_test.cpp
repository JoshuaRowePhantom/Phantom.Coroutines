#include <gtest/gtest.h>
#include "Phantom.Coroutines/atomic_state.h"

namespace Phantom::Coroutines
{
namespace
{
struct Label1 {};
struct Label2 {};
struct Incomplete {};
struct HasException {};
struct HasResult {};

struct PointedToValue {};

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>
> test_atomic_state_with_singletons;

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>,
    StateSet<struct WaitingCoroutine, PointedToValue*>
> test_atomic_state_with_pointer_set;

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>,
    StateSet<struct WaitingCoroutine, coroutine_handle<>>
> test_atomic_state_with_set;

typedef atomic_state<
    SingletonState<struct Incomplete>,
    SingletonState<struct HasException>,
    SingletonState<struct HasResult>,
    StateSet<struct WaitingRoutine, coroutine_handle<>>,
    StateSet<struct SomethingElse, SomethingElse*>
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

TEST(atomic_state_test, Can_store_pointer_values_into_state_with_set)
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

    state.store(Label2());
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value == Label2());
    ASSERT_TRUE(value != &value1);
    ASSERT_TRUE(value != &value2);
    ASSERT_TRUE(value.is_singleton());

    state.store(&value1);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value == &value1);
    ASSERT_TRUE(value != &value2);
    ASSERT_TRUE(!value.is_singleton());

    state.store(&value2);
    value = state.load();
    ASSERT_TRUE(value != Label1());
    ASSERT_TRUE(value != Label2());
    ASSERT_TRUE(value != &value1);
    ASSERT_TRUE(value == &value2);
    ASSERT_TRUE(!value.is_singleton());
}

}
