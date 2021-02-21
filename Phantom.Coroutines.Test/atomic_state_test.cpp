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

typedef atomic_state<
    SingletonState<struct Label1>,
    SingletonState<struct Label2>,
    StateSet<struct WaitingCoroutine, coroutine_handle<>>
> test_atomic_state_with_set;

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

TEST(atomic_state_test, Can_create_and_destroy_state_with_set)
{
    test_atomic_state_with_set state
    {
        Label2()
    };
}
}
