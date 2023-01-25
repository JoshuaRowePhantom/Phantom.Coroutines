#include <string>
#include <type_traits>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/type_traits.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "lifetime_tracker.h"
#include "async_test.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(detail::is_awaiter<task_awaiter<task_promise<void>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<int>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<int&>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<int&&>>>);

static_assert(detail::is_awaitable<task<>>);
static_assert(detail::is_awaitable<task<int>>);
static_assert(detail::is_awaitable<task<int&>>);
static_assert(detail::is_awaitable<task<int&&>>);

static_assert(detail::is_awaiter<task_awaiter<task_promise<void>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<std::string>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<std::string&>>>);
static_assert(detail::is_awaiter<task_awaiter<task_promise<std::string&&>>>);

static_assert(detail::is_awaitable<task<>>);
static_assert(detail::is_awaitable<task<std::string>>);
static_assert(detail::is_awaitable<task<std::string&>>);
static_assert(detail::is_awaitable<task<std::string&&>>);

static_assert(detail::has_co_await_member<task<>&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<task<>>, void>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>>, int&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&>>, int&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<int&&>>, int&&>);

static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string>>, std::string&&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string&>>, std::string&>);
static_assert(std::same_as<detail::awaitable_result_type_t<task<std::string&&>>, std::string&&>);

TEST(task_test, Can_await_void_task)
{
    sync_wait(
        []() -> task<>
    {
        co_return;
    }()
    );
}

TEST(task_test, Can_handle_thrown_exception)
{
    ASSERT_THROW(
        {
            sync_wait(
                []() -> task<>
            {
                throw 5;
                co_return;
            }()
                );
        },
        int);
}

TEST(task_test, Can_await_string_task)
{
    auto result = sync_wait(
        []() -> task<std::string>
    {
        co_return "hello world";
    }());

    ASSERT_EQ("hello world", result);
}

TEST(task_test, Can_return_reference)
{
    int value = 1;

    auto& result = sync_wait(
        [&]() -> task<int&>
    {
        co_return value;
    }());

    ASSERT_EQ(&value, &result);
}

TEST(task_test, Returned_object_is_by_rvalue_reference_to_caller_in_rvalue_context)
{
    lifetime_statistics statistics;
    std::optional<lifetime_statistics> intermediateStatistics;

    auto myLambda = [&](lifetime_tracker&& tracker)
    {};

    auto myInnerTask = [&]() -> task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    auto myOuterTask = [&]() -> task<>
    {
        myLambda(co_await std::move(myInnerTask()));
        intermediateStatistics = statistics;
    };

    sync_wait(
        myOuterTask());

    ASSERT_EQ(1, intermediateStatistics->move_construction_count);
    ASSERT_EQ(0, intermediateStatistics->copy_construction_count);
    ASSERT_EQ(0, intermediateStatistics->instance_count);
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

    ASSERT_EQ(0, statistics.instance_count);
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

    ASSERT_EQ(0, statistics.instance_count);
}

TEST(task_test, Can_return_rvalue_reference_Address_doesnt_change)
{
    std::string value = "hello world";
    std::string* finalAddress = nullptr;

    sync_wait([&]() -> task<>
    {
        auto& v = reinterpret_cast<std::string&>(co_await[&]() -> task<std::string&&>
        {
            co_return value;
        }());

        finalAddress = &v;
    }());

    ASSERT_EQ(&value, finalAddress);
}

TEST(task_test, Can_use_returned_rvalue_reference)
{
    detail::lifetime_statistics statistics;
    detail::lifetime_tracker initialValue = statistics.tracker();

    sync_wait([&]() -> task<>
    {
        auto endValue = co_await[&]() -> task<detail::lifetime_tracker&&>
        {
            co_return initialValue;
        }();

        [&]() {
            ASSERT_EQ(2, statistics.instance_count);
            ASSERT_EQ(1, statistics.move_construction_count);
        }();
    }());

    ASSERT_TRUE(initialValue.moved_from());
    ASSERT_EQ(1, statistics.instance_count);
}

TEST(task_test, Can_use_returned_rvalue_reference_with_same_address)
{
    detail::lifetime_statistics statistics;
    detail::lifetime_tracker initialValue = statistics.tracker();

    sync_wait([&]() -> task<>
    {
        [&](detail::lifetime_tracker&& endValue) {

            endValue.use();
            ASSERT_EQ(1, statistics.instance_count);
            ASSERT_EQ(0, statistics.move_construction_count);
        }(
            co_await[&]() -> task<detail::lifetime_tracker&&>
        {
            co_return initialValue;
        }());
    }());

    ASSERT_FALSE(initialValue.moved_from());
    ASSERT_EQ(1, statistics.instance_count);
    ASSERT_FALSE(statistics.used_after_move);
}

TEST(task_test, Can_suspend_and_resume)
{
    async_manual_reset_event<> event;
    int stage = 0;

    auto future = as_future(
        [&]() -> task<>
    {
        stage = 1;
        co_await event;
        stage = 2;
    }());

    ASSERT_EQ(1, stage);
    event.set();
    ASSERT_EQ(2, stage);
}

TEST(task_test, Can_loop_without_stackoverflow)
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

    auto actualSum = sync_wait(
        outerTaskLambda());
    ASSERT_EQ(1000000, actualSum);
}

TEST(task_test, Destroys_returned_value)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> task<lifetime_tracker>
    {
        co_return statistics.tracker();
    };

    sync_wait([&]() -> task<>
    {
        {
            auto tracker = co_await taskWithReturnValueLambda();
            instanceCountBeforeDestruction = statistics.instance_count;
        }
        instanceCountAfterDestruction = statistics.instance_count;
    }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}

TEST(task_test, Destroys_thrown_exception)
{
    lifetime_statistics statistics;
    std::optional<size_t> instanceCountBeforeDestruction;
    std::optional<size_t> instanceCountAfterDestruction;

    auto taskWithReturnValueLambda = [&]() -> task<int>
    {
        throw statistics.tracker();
        co_return 5;
    };

    sync_wait([&]() -> task<>
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
    }());

    ASSERT_EQ(1, instanceCountBeforeDestruction);
    ASSERT_EQ(0, instanceCountAfterDestruction);
}
