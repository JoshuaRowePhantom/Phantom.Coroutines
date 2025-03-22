#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.async_auto_reset_event;
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.reusable_task;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.Test.lifetime_tracker;
import Phantom.Coroutines.Test.pmr_task;
#else
#include "Phantom.Coroutines/async_auto_reset_event.h"
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/type_traits.h"
#include "Phantom.Coroutines/reusable_task.h"
#include "lifetime_tracker.h"
#include "pmr_task.h"
#endif
#include "Phantom.Coroutines/suspend_result.h"
#include "async_test.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(!std::is_copy_constructible_v<reusable_task<>>);
static_assert(!std::is_copy_assignable_v<reusable_task<>>);
static_assert(std::is_move_constructible_v<reusable_task<>>);
static_assert(std::is_move_assignable_v<reusable_task<>>);

static_assert(detail::is_awaitable<reusable_task<>>);
static_assert(detail::is_awaitable<reusable_task<int>>);
static_assert(detail::is_awaitable<reusable_task<int&>>);
static_assert(detail::is_awaitable<reusable_task<int&&>>);

static_assert(has_co_await_member<reusable_task<>>);
static_assert(has_co_await_member<reusable_task<>&>);
static_assert(has_co_await_member<reusable_task<>&&>);

static_assert(detail::is_awaitable<reusable_task<>&>);
static_assert(detail::is_awaitable<reusable_task<int>&>);
static_assert(detail::is_awaitable<reusable_task<int&>&>);
static_assert(detail::is_awaitable<reusable_task<int&&>&>);

static_assert(detail::has_co_await_member<reusable_task<>&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<>>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&&>>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&&>>, int&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<>&>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&&>&>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&>&>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<int&&>&>, int&&>);
// Awaiting r-values of reusable_task should
// return values as r-value references
// and other references as the underlying type.
static_assert(std::same_as<decltype(std::declval<awaiter_type<reusable_task<std::string>>>().await_resume()), std::string&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string>>, std::string&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&>>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&&>>, std::string&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string>&&>, std::string&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&>&&>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&&>&&>, std::string&&>);

// Awaiting l-values of reusable_task should
// return value as l-value references 
// and other references as the underlying type.
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string>&>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&>&>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<reusable_task<std::string&&>&>, std::string&&>);

ASYNC_TEST(reusable_task_test, Can_await_void_reusable_task)
{
    co_await 
        []() -> reusable_task<>
    {
        co_return;
    }();
}

ASYNC_TEST(reusable_task_test, Can_handle_thrown_exception)
{
    EXPECT_THROW(
        {
            co_await (
                []() -> reusable_task<>
            {
                throw 5;
                co_return;
            }()
                );
        },
        int);
}

ASYNC_TEST(reusable_task_test, Can_await_string_reusable_task)
{
    auto result = co_await
        []() -> reusable_task<std::string>
    {
        co_return "hello world";
    }();

    EXPECT_EQ("hello world", result);
}

ASYNC_TEST(reusable_task_test, Can_return_reference)
{
    int value = 1;

    auto& result = co_await
        [&]() -> reusable_task<int&>
    {
        co_return value;
    }();

    EXPECT_EQ(&value, &result);
}

ASYNC_TEST(reusable_task_test, Returned_object_is_by_rvalue_reference_to_caller_in_rvalue_context)
{
    lifetime_statistics statistics;
    std::optional<lifetime_statistics> intermediateStatistics;

    auto myLambda = [&](lifetime_tracker&&)
    {};

    auto myInnerreusable_task = [&]() -> reusable_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto myOuterreusable_task = [&]() -> reusable_task<>
    {
        myLambda(co_await std::move(myInnerreusable_task()));
        intermediateStatistics = statistics;
    };

    co_await myOuterreusable_task();

    EXPECT_EQ(1, intermediateStatistics->move_construction_count);
    EXPECT_EQ(0, intermediateStatistics->copy_construction_count);
    EXPECT_EQ(0, intermediateStatistics->instance_count);
}

TEST(reusable_task_test, reusable_task_destroys_coroutine_if_not_awaited)
{
    lifetime_statistics statistics;
    async_manual_reset_event<> event;

    {
        // Create a reusable_task and destroy it
        auto myreusable_task = [&, tracker = statistics.tracker()]()->reusable_task<>
        {
            tracker.use();
            co_return;
        }();
    }

    ASSERT_EQ(0, statistics.instance_count);
}

namespace
{

template<
    typename Result
> class lifetime_tracking_reusable_task_promise :
    public derived_promise<reusable_task_promise<Result>>
{
    lifetime_tracker m_tracker;

public:
    lifetime_tracking_reusable_task_promise(
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
> using lifetime_tracking_reusable_task = basic_reusable_task<lifetime_tracking_reusable_task_promise<Result>>;

static_assert(std::same_as<lifetime_tracking_reusable_task_promise<void>, lifetime_tracking_reusable_task<>::promise_type>);
static_assert(std::same_as<lifetime_tracking_reusable_task_promise<void>, std::coroutine_traits<lifetime_tracking_reusable_task<>, lifetime_tracker>::promise_type>);

}

ASYNC_TEST(reusable_task_test, reusable_task_destroys_coroutine_after_resumption_of_calling_coroutine)
{
    lifetime_statistics statistics;

    auto lambda1 = [&](lifetime_tracker) -> lifetime_tracking_reusable_task<int>
    {
        EXPECT_EQ(2, statistics.instance_count);
        co_return 5;
    };

    auto lambda2 = [&](int) -> reusable_task<>
    {
        EXPECT_EQ(2, statistics.instance_count);
        co_return;
    };

    co_await lambda2(
        co_await lambda1(statistics.tracker()));
    EXPECT_EQ(0, statistics.instance_count);
}

TEST(reusable_task_test, reusable_task_destroys_coroutine_if_destroyed_while_suspended)
{
    lifetime_statistics statistics;
    async_manual_reset_event<> event;

    {
        // Create and suspend a reusable_task, then destroy it.
        auto myreusable_task = [&]() -> reusable_task<>
        {
            auto tracker = statistics.tracker();
            co_await event;
        }();

        auto awaiter = std::move(myreusable_task).operator co_await();

        auto coroutine = awaiter.await_suspend(
            noop_coroutine()
        );

        // This will reach the first suspend point.
        coroutine.resume();

        // This will destroy the awaiter.
    }

    ASSERT_EQ(0, statistics.instance_count);
}

ASYNC_TEST(reusable_task_test, Can_return_rvalue_reference_Address_doesnt_change)
{
    std::string value = "hello world";
    std::string* finalAddress = nullptr;

    co_await [&]() -> reusable_task<>
    {
        auto&& v = std::move(co_await[&]() -> reusable_task<std::string&&>
        {
            co_return std::move(value);
        }());

        finalAddress = &v;
    }();

    EXPECT_EQ(&value, finalAddress);
}

ASYNC_TEST(reusable_task_test, Can_use_returned_rvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker initialValue = statistics.tracker();

    co_await [&]() -> reusable_task<>
    {
        auto endValue = co_await[&]() -> reusable_task<lifetime_tracker&&>
    {
        co_return std::move(initialValue);
    }();

    [&]() {
        EXPECT_EQ(2, statistics.instance_count);
        EXPECT_EQ(1, statistics.move_construction_count);
    }();
    }();

    EXPECT_TRUE(initialValue.moved_from());
    EXPECT_EQ(1, statistics.instance_count);
}

ASYNC_TEST(reusable_task_test, Can_use_returned_rvalue_reference_with_same_address)
{
    lifetime_statistics statistics;
    lifetime_tracker initialValue = statistics.tracker();

    co_await [&]() -> reusable_task<>
    {
        [&](lifetime_tracker&& endValue) {

            endValue.use();
            ASSERT_EQ(1, statistics.instance_count);
            ASSERT_EQ(0, statistics.move_construction_count);
        }(
            co_await[&]() -> reusable_task<lifetime_tracker&&>
        {
            co_return std::move(initialValue);
        }());
    }();

    EXPECT_FALSE(initialValue.moved_from());
    EXPECT_EQ(1, statistics.instance_count);
    EXPECT_FALSE(statistics.used_after_move);
}

TEST(reusable_task_test, Can_suspend_and_resume)
{
    async_manual_reset_event<> event;
    int stage = 0;

    async_scope<> scope;
    scope.spawn([&]() -> reusable_task<>
    {
        stage = 1;
        co_await event;
        stage = 2;
    });

    ASSERT_EQ(1, stage);
    event.set();
    ASSERT_EQ(2, stage);
}

ASYNC_TEST(reusable_task_test, Can_loop_without_stackoverflow)
{
    auto innerreusable_taskLambda = []() -> reusable_task<int> { co_return 1; };
    auto outerreusable_taskLambda = [&]() -> reusable_task<int>
    {
        auto sum = 0;

        for (int counter = 0; counter < 1000000; counter++)
        {
            sum += co_await innerreusable_taskLambda();
        }

        co_return sum;
    };

    auto actualSum = co_await outerreusable_taskLambda();
    EXPECT_EQ(1000000, actualSum);
}

ASYNC_TEST(reusable_task_test, Destroys_returned_value)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto innerTask = [&]() -> reusable_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto outerTask = [&]() -> reusable_task<>
    {
        auto task = std::optional{ innerTask() };
        auto tracker = co_await *task;
        instanceCountBeforeDestruction = statistics.instance_count;
        task.reset();
        instanceCountAfterDestruction = statistics.instance_count;
    };

    co_await outerTask();

    EXPECT_EQ(2, instanceCountBeforeDestruction);
    EXPECT_EQ(1, instanceCountAfterDestruction);
}

ASYNC_TEST(reusable_task_test, Destroys_thrown_exception)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto reusable_taskWithReturnValueLambda = [&]() -> reusable_task<int>
    {
        throw statistics.tracker();
        co_return 5;
    };

    co_await ([&]() -> reusable_task<>
    {
        {
            auto reusable_task = reusable_taskWithReturnValueLambda();
            try
            {
                co_await reusable_task;
            }
            catch (lifetime_tracker&)
            {
                instanceCountBeforeDestruction = statistics.instance_count;
            }
        }
        instanceCountAfterDestruction = statistics.instance_count;
    }());

    EXPECT_EQ(2, instanceCountBeforeDestruction);
    EXPECT_EQ(0, instanceCountAfterDestruction);
}

ASYNC_TEST(reusable_task_test, Can_be_awaited_twice)
{
    lifetime_statistics statistics;

    auto lambda = [&]() -> reusable_task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto task = lambda();

    auto& tracker1 = co_await task;
    auto& tracker2 = co_await task;
    EXPECT_EQ(&tracker1, &tracker2);
    EXPECT_EQ(tracker1, statistics);
}

ASYNC_TEST(reusable_task_test, Can_await_twice_within_promise)
{
    lifetime_statistics statistics;
    async_auto_reset_event<> event;
    bool reached1 = false;
    bool reached2 = false;

    auto lambda = [&]() -> reusable_task<>
    {
        co_await event;
        reached1 = true;
        co_await event;
        reached2 = true;
    };
    async_scope<> scope;
    scope.spawn(lambda());

    EXPECT_FALSE(reached1);
    event.set();
    EXPECT_TRUE(reached1);
    EXPECT_FALSE(reached2);
    event.set();
    EXPECT_TRUE(reached2);

    co_await scope.join();
}

ASYNC_TEST(reusable_task_test, when_ready_does_not_throw_exception)
{
    auto lambda = [&]() -> reusable_task<std::string>
    {
        throw 0;
        co_return{};
    };

    auto task = lambda();
    co_await task.when_ready();

    try
    {
        co_await task;
        EXPECT_TRUE(false);
    }
    catch (int)
    {
    }
}

namespace
{
using Test::pmr_reusable_task;
using Test::memory_tracker;
}

ASYNC_TEST(reusable_task_test, DISABLED_can_elide_allocations)
{
    memory_tracker tracker;
    std::pmr::polymorphic_allocator<> allocator(&tracker);

    size_t outerAllocation;
    size_t innerAllocation;

    auto inner = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_reusable_task<>
    {
        innerAllocation = tracker.allocated_memory();
        co_return;
    };

    auto outer = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_reusable_task<>
    {
        outerAllocation = tracker.allocated_memory();
        co_await inner(allocator);
    };

    co_await outer(allocator);
#if NDEBUG
    EXPECT_EQ(innerAllocation, outerAllocation);
#endif
}

ASYNC_TEST(reusable_task_test, destroys_coroutine_when_awaited_as_rvalue)
{
    memory_tracker tracker;
    std::pmr::polymorphic_allocator<> allocator(&tracker);

    size_t outerAllocation1;
    size_t outerAllocation2;

    auto inner = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_reusable_task<>
    {
        co_return;
    };

    auto outer = [&](std::pmr::polymorphic_allocator<> allocator) -> pmr_reusable_task<>
    {
        outerAllocation1 = tracker.allocated_memory();
        co_await inner(allocator);
        outerAllocation2 = tracker.allocated_memory();
    };

    co_await outer(allocator);
    EXPECT_EQ(outerAllocation1, outerAllocation2);
}

ASYNC_TEST(reusable_task_test, second_await_on_task_does_not_suspend)
{
    auto lambda = [&]() -> reusable_task<std::string>
    {
        co_return "hello world";
    };
    auto task = lambda();

    suspend_result suspendResult;
    auto result1 = co_await(suspendResult << task);
    EXPECT_EQ(true, suspendResult.did_suspend());
    suspendResult.reset();
    auto result2 = co_await(suspendResult << task);
    EXPECT_EQ(false, suspendResult.did_suspend());
}

ASYNC_TEST(reusable_task_test, make_reusable_task_from_value_is_completed)
{
    auto task = make_reusable_task_from_value(std::string("hello world"));
    suspend_result suspendResult;
    auto result = co_await(suspendResult << task);
    EXPECT_EQ(false, suspendResult.did_suspend());
    EXPECT_EQ(std::string("hello world"), result);
}

ASYNC_TEST(reusable_task_test, make_reusable_task_from_void_is_completed)
{
    auto task = make_reusable_task_from_void();
    suspend_result suspendResult;
    co_await(suspendResult << task);
    EXPECT_EQ(false, suspendResult.did_suspend());
}
