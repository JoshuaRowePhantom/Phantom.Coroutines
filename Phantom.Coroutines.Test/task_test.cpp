#if 0
#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/task.h"
#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.Test.lifetime_tracker;
import Phantom.Coroutines.Test.pmr_task;
#else
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/type_traits.h"
#include "lifetime_tracker.h"
#include "pmr_task.h"
#endif

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(!std::is_copy_constructible_v<task<>>);
static_assert(!std::is_copy_assignable_v<task<>>);
static_assert(std::is_move_constructible_v<task<>>);
static_assert(std::is_move_assignable_v<task<>>);

static_assert(detail::is_awaiter<decltype(std::declval<task<task_promise<void>>>().operator co_await())>);
static_assert(detail::is_awaiter<decltype(std::declval<task<task_promise<int>>>().operator co_await())>);
static_assert(detail::is_awaiter<decltype(std::declval<task<task_promise<int&>>>().operator co_await())>);
static_assert(detail::is_awaiter<decltype(std::declval<task<task_promise<int&&>>>().operator co_await())>);

// tasks are awaitable
static_assert(detail::is_awaitable<task<>>);
static_assert(detail::is_awaitable<task<int>>);
static_assert(detail::is_awaitable<task<int&>>);
static_assert(detail::is_awaitable<task<int&&>>);
// l-value references to tasks are not awaitable
static_assert(!detail::is_awaitable<task<>&>);
static_assert(!detail::is_awaitable<task<int>&>);
static_assert(!detail::is_awaitable<task<int&>&>);
static_assert(!detail::is_awaitable<task<int&&>&>);
// r-value references to tasks are awaitable
static_assert(detail::is_awaitable<task<>&&>);
static_assert(detail::is_awaitable<task<int>&&>);
static_assert(detail::is_awaitable<task<int&>&&>);
static_assert(detail::is_awaitable<task<int&&>&&>);

static_assert(detail::has_co_await_member<task<>&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<task<>>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int>>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>>, int&&>);
// These are not valid, as task<>& is not awaitable.
// static_assert(std::same_as<detail::awaitable_result_type_t<task<int>&>, int&&>);
// static_assert(std::same_as<detail::awaitable_result_type_t<task<int&>&>, int&>);
// static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>&>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int>&&>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&>&&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>&&>, int&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string>>, std::string&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string&>>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string&&>>, std::string&&>);

ASYNC_TEST(task_test, Can_await_void_task)
{
    co_await (
        []() -> task<>
    {
        co_return;
    }()
    );
}

ASYNC_TEST(task_test, Can_handle_thrown_exception)
{
    EXPECT_THROW(
        {
            co_await(
                []() -> task<>
            {
                throw 5;
                co_return;
            }()
                );
        },
        int);
}

ASYNC_TEST(task_test, Can_await_string_task)
{
    auto result = co_await(
        []() -> task<std::string>
    {
        co_return "hello world";
    }());

    EXPECT_EQ("hello world", result);
}

ASYNC_TEST(task_test, Can_return_reference)
{
    int value = 1;

    auto& result = co_await(
        [&]() -> task<int&>
    {
        co_return value;
    }());

    EXPECT_EQ(&value, &result);
}

ASYNC_TEST(task_test, Returned_object_is_by_rvalue_reference_to_caller_in_rvalue_context)
{
    lifetime_statistics statistics;
    std::optional<lifetime_statistics> intermediateStatistics;

    auto myLambda = [&](lifetime_tracker&& tracker)
    {
        std::ignore = tracker;
    };

    auto myInnerTask = [&]() -> task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto myOuterTask = [&]() -> task<>
    {
        myLambda(co_await std::move(myInnerTask()));
        intermediateStatistics = statistics;
    };

    co_await(
        myOuterTask());

    EXPECT_EQ(1, intermediateStatistics->move_construction_count);
    EXPECT_EQ(0, intermediateStatistics->copy_construction_count);
    EXPECT_EQ(0, intermediateStatistics->instance_count);
}

TEST(task_test, Task_destroys_coroutine_if_not_awaited)
{
    lifetime_statistics statistics;
    async_manual_reset_event<> event;

    {
        // Create a task and destroy it
        auto myTask = [&, tracker = statistics.tracker()]()->task<>
        {
            tracker.use();
            co_return;
        }();
    }

    EXPECT_EQ(0, statistics.instance_count);
}

namespace
{

template<
    typename Result
> class lifetime_tracking_task_promise : 
    public derived_promise<task_promise<Result>>
{
    lifetime_tracker m_tracker;

public:
    lifetime_tracking_task_promise(
        auto&&... args
    ) :
        m_tracker
    { 
        get<lifetime_tracker&>(std::tie(args...))
    }
    {}
};

template<
    typename Result = void
> using lifetime_tracking_task = basic_task<lifetime_tracking_task_promise<Result>>;

static_assert(std::same_as<lifetime_tracking_task_promise<void>, lifetime_tracking_task<>::promise_type>);
static_assert(std::same_as<lifetime_tracking_task_promise<void>, std::coroutine_traits<lifetime_tracking_task<>, lifetime_tracker>::promise_type>);

}

ASYNC_TEST(task_test, Task_destroys_coroutine_before_resumption_of_calling_coroutine)
{
    lifetime_statistics statistics;

    auto lambda1 = [&](lifetime_tracker) -> lifetime_tracking_task<int>
    {
        EXPECT_EQ(2, statistics.instance_count);
        co_return 5;
    };

    auto lambda2 = [&](int) -> task<>
    {
        EXPECT_EQ(0, statistics.instance_count);
        co_return;
    };

    co_await lambda2(
        co_await lambda1(statistics.tracker()));
}

TEST(task_test, Task_destroys_coroutine_if_destroyed_while_suspended)
{
    lifetime_statistics statistics;
    async_manual_reset_event<> event;

    {
        // Create and suspend a task, then destroy it.
        auto myTask = [&]() -> task<>
        {
            auto tracker = statistics.tracker();
            co_await event;
        }();

        auto awaiter = std::move(myTask).operator co_await();

        auto coroutine = awaiter.await_suspend(
            std::noop_coroutine()
        );

        // This will reach the first suspend point.
        coroutine.resume();

        // This will destroy the awaiter.
    }

    EXPECT_EQ(0, statistics.instance_count);
}

ASYNC_TEST(task_test, Can_return_rvalue_reference_Address_doesnt_change)
{
    std::string value = "hello world";
    std::string* finalAddress = nullptr;

    co_await([&]() -> task<>
    {
        auto&& v = std::move(co_await[&]() -> task<std::string&&>
        {
            co_return std::move(value);
        }());

        finalAddress = &v;
    }());

    EXPECT_EQ(&value, finalAddress);
}

ASYNC_TEST(task_test, Can_use_returned_rvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker initialValue = statistics.tracker();

    co_await([&]() -> task<>
    {
        auto endValue = co_await[&]() -> task<lifetime_tracker&&>
        {
            co_return std::move(initialValue);
        }();

        [&]() {
            EXPECT_EQ(2, statistics.instance_count);
            EXPECT_EQ(1, statistics.move_construction_count);
        }();
    }());

    EXPECT_TRUE(initialValue.moved_from());
    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(task_test, Can_use_returned_rvalue_reference_with_same_address)
{
    lifetime_statistics statistics;
    lifetime_tracker initialValue = statistics.tracker();

    co_await([&]() -> task<>
    {
        [&](lifetime_tracker&& endValue) {

            endValue.use();
            EXPECT_EQ(1, statistics.instance_count);
            EXPECT_EQ(0, statistics.move_construction_count);
        }(
            co_await[&]() -> task<lifetime_tracker&&>
        {
            co_return std::move(initialValue);
        }());
    }());

    EXPECT_FALSE(initialValue.moved_from());
    EXPECT_EQ(1, statistics.instance_count);
    EXPECT_FALSE(statistics.used_after_move);
}

ASYNC_TEST(task_test, Can_suspend_and_resume)
{
    async_manual_reset_event<> event;
    int stage = 0;

    auto lambda = [&]() -> task<>
    {
        stage = 1;
        co_await event;
        stage = 2;
    };

    async_scope<> scope;
    scope.spawn(
        lambda());

    EXPECT_EQ(1, stage);
    event.set();
    EXPECT_EQ(2, stage);
    co_await scope.join();
}

ASYNC_TEST(task_test, Can_loop_without_stackoverflow)
{
    auto innerTaskLambda = []() -> task<int> { co_return 1; };
    auto outerTaskLambda = [&]() -> task<int>
    {
        auto sum = 0;

        for (int counter = 0; counter < 1000000; counter++)
        {
            sum += co_await innerTaskLambda();
        }

        co_return sum;
    };

    auto actualSum = co_await(
        outerTaskLambda());
    EXPECT_EQ(1000000, actualSum);
}

ASYNC_TEST(task_test, Destroys_returned_value)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    co_await([&]() -> task<>
    {
        {
            auto tracker = co_await taskWithReturnValueLambda();
            instanceCountBeforeDestruction = statistics.instance_count;
        }
        instanceCountAfterDestruction = statistics.instance_count;
    }());

    EXPECT_EQ(1, instanceCountBeforeDestruction);
    EXPECT_EQ(0, instanceCountAfterDestruction);
}

ASYNC_TEST(task_test, Destroys_thrown_exception)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> task<int>
    {
        throw statistics.tracker();
        co_return 5;
    };

    auto outerTask = [&]() -> task<>
    {
        {
            auto task = taskWithReturnValueLambda();
            try
            {
                co_await std::move(task);
            }
            catch (lifetime_tracker &)
            {
                instanceCountBeforeDestruction = statistics.instance_count;
            }
        }
        instanceCountAfterDestruction = statistics.instance_count;
    };

    co_await outerTask();

    EXPECT_EQ(1, instanceCountBeforeDestruction);
    EXPECT_EQ(0, instanceCountAfterDestruction);
}

namespace
{
using Test::pmr_task;
using Test::memory_tracker;
}

ASYNC_TEST(task_test, DISABLED_can_elide_allocations)
{
    memory_tracker tracker;
    std::pmr::polymorphic_allocator<> allocator(&tracker);

    size_t outerAllocation;
    size_t innerAllocation;

    auto inner = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_task<>
    {
        innerAllocation = tracker.allocated_memory();
        co_return;
    };

    auto outer = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_task<>
    {
        outerAllocation = tracker.allocated_memory();
        co_await inner(allocator);
    };

    co_await outer(allocator);
#if NDEBUG
    EXPECT_EQ(innerAllocation, outerAllocation);
#endif
}
#endif
