#include "async_test.h"
#include <expected>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.await_all_await_transform;
import Phantom.Coroutines.early_termination_task;
import Phantom.Coroutines.error_condition_early_termination;
import Phantom.Coroutines.expected_early_termination;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/await_all_await_transform.h"
#include "Phantom.Coroutines/early_termination_task.h"
#include "Phantom.Coroutines/error_condition_early_termination.h"
#include "Phantom.Coroutines/expected_early_termination.h"
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/type_traits.h"
#include "lifetime_tracker.h"
#endif

namespace Phantom::Coroutines
{
namespace
{
template<
    typename Value = void,
    typename Error = int
> using expected_early_termination_task =
early_termination_task<
    std::expected<Value, Error>,
    expected_early_termination_result,
    expected_early_termination_transformer
>;

}

static_assert(is_early_termination_policy<expected_early_termination_result>);
static_assert(is_early_termination_policy<expected_early_termination_transformer>);
static_assert(detail::early_termination_policy_selector<expected_early_termination_result>::value);
static_assert(detail::early_termination_policy_selector<expected_early_termination_transformer>::value);

template<
    typename T,
    typename Expected
>
struct assert_is_type
{
    static_assert(std::same_as<T, Expected>);
    static constexpr bool value = true;
};

static_assert(assert_is_type<
    typename detail::filter_types<
        detail::early_termination_policy_selector,
        expected_early_termination_result, 
        expected_early_termination_transformer
    >::tuple_type,

    std::tuple<
        expected_early_termination_result, 
        expected_early_termination_transformer
    >
>::value);

static_assert(assert_is_type<
        expected_early_termination_task<void>,
        detail::basic_early_termination_task<
            detail::early_termination_promise_inheritor<
                detail::basic_early_termination_promise<
                    task_promise<std::expected<void, int>>
                >,
                std::tuple<
                    expected_early_termination_result,
                    expected_early_termination_transformer
                >,
                std::tuple<
                    expected_early_termination_transformer
                >
            >
        >
    >::value);

ASYNC_TEST(expected_early_termination_test, co_await_expected_with_value_continues_top_level_coroutine)
{
    auto lambda = [&]() -> expected_early_termination_task<void>
    {
        std::string result = co_await std::expected<std::string, int>("hello world");
        EXPECT_EQ(result, "hello world");
        co_return{};
    };

    auto result = co_await lambda().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>()));
}

ASYNC_TEST(expected_early_termination_test, co_await_expected_with_error_terminates_top_level_coroutine)
{
    auto lambda = [&]() -> expected_early_termination_task<void>
    {
        std::string result = co_await std::expected<std::string, int>(std::unexpect, 1);
        // We should not reach here.
        EXPECT_TRUE(false);
        co_return{};
    };

    auto result = co_await lambda().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>(std::unexpect, 1)));
}

ASYNC_TEST(expected_early_termination_test, co_return_unexpected_terminates_nested_coroutines)
{
    auto lambda1 = [&]() -> expected_early_termination_task<void>
    {
        co_return std::unexpected{ 1 };
    };

    auto lambda2 = [&]() -> expected_early_termination_task<void>
    {
        co_await lambda1();
        EXPECT_TRUE(false);
        co_return{};
    };

    auto result = co_await lambda2().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>(std::unexpect, 1)));
}

ASYNC_TEST(expected_early_termination_test, co_return_expected_with_error_terminates_nested_coroutines)
{
    auto lambda1 = [&]() -> expected_early_termination_task<void>
    {
        co_return std::expected<void, int>{ std::unexpect, 1 };
    };

    auto lambda2 = [&]() -> expected_early_termination_task<void>
    {
        co_await lambda1();
        EXPECT_TRUE(false);
        co_return{};
    };

    auto result = co_await lambda2().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>(std::unexpect, 1)));
}

ASYNC_TEST(expected_early_termination_test, co_await_expected_with_value_continues_nested_coroutines_of_different_types)
{
    auto lambda1 = [&]() -> expected_early_termination_task<int>
    {
        co_return 5;
    };

    auto lambda2 = [&]() -> expected_early_termination_task<long>
    {
        auto result = co_await lambda1();
        EXPECT_EQ(result, 5);
        co_return 6;
    };

    auto result = co_await lambda2().handle_errors();
    EXPECT_EQ(result, (std::expected<long, int>(6)));
}

ASYNC_TEST(expected_early_termination_test, co_await_expected_handle_errors_with_value_continues_nested_coroutines_of_different_types)
{
    auto lambda1 = [&]() -> expected_early_termination_task<int>
    {
        co_return 5;
    };

    auto lambda2 = [&]() -> expected_early_termination_task<long>
    {
        auto result = co_await lambda1().handle_errors();
        static_assert(std::same_as<std::expected<int, int>, decltype(result)>);
        EXPECT_EQ(result, (std::expected<long, int>{ 5 }));
        co_return 6;
    };

    auto result = co_await lambda2().handle_errors();
    EXPECT_EQ(result, (std::expected<long, int>(6)));
}

ASYNC_TEST(expected_early_termination_test, error_causes_coroutine_to_be_destroyed_before_resuming_caller)
{
    lifetime_statistics statistics;

    auto lambda1 = [&]() -> expected_early_termination_task<>
    {
        auto tracker = statistics.tracker();
        EXPECT_EQ(statistics.instance_count, 1);
        co_await std::expected<int, int> { std::unexpected{ 5 } };
        EXPECT_TRUE(false);
        co_return{};
    };

    auto lambda2 = [&](std::expected<void, int> result) -> task<>
    {
        EXPECT_EQ(statistics.instance_count, 0);
        co_return;
    };

    co_await lambda2(
        co_await lambda1().handle_errors()
    );
}

ASYNC_TEST(expected_early_termination_test, exception_terminates_nested_coroutines_without_invoking_exception_handlers)
{
    auto lambda1 = [&]() -> expected_early_termination_task<>
    {
        throw std::string("hello world");
        EXPECT_TRUE(false);
        co_return{};
    };

    auto lambda2 = [&]() -> expected_early_termination_task<>
    {
        try
        {
            co_await lambda1();
            EXPECT_TRUE(false);
        }
        catch (...)
        {
            EXPECT_TRUE(false);
        }
        co_return{};
    };

    auto lambda3 = [&]() -> expected_early_termination_task<>
    {
        try
        {
            co_await lambda2();
        }
        catch (...)
        {
            EXPECT_TRUE(false);
        }
        EXPECT_TRUE(false);
        co_return{};
    };
    
    try
    {
        co_await lambda3().handle_errors();
    }
    catch (std::string& actualException)
    {
        EXPECT_EQ(std::string("hello world"), actualException);
    }
}

namespace
{
template<
    typename Result
> using expected_early_termination_ordinary_task = 
basic_task<
    derived_promise<
        task_promise<
            std::expected<Result, int>
        >,
        expected_early_termination_transformer,
        await_all_await_transform
    >
>;
}

ASYNC_TEST(expected_early_termination_ordinary_task_test, can_complete_task_and_resume_caller_with_error)
{
    auto lambda1 = [&]() -> expected_early_termination_ordinary_task<std::string>
    {
        co_await std::expected<std::string, int>(std::unexpect, 5);
        EXPECT_EQ(false, true);
        co_return "Hello world";
    };

    derived_promise<
        task_promise<
        std::expected<long, int>
        >,
        expected_early_termination_transformer,
        await_all_await_transform
    > p;
    p.await_transform(std::expected<int, int>());

    auto lambda2 = [&]() -> expected_early_termination_ordinary_task<long>
    {
        auto result = co_await lambda1();
        static_assert(std::same_as<std::expected<std::string, int>, decltype(result)>);
        EXPECT_EQ(result, (std::expected<std::string, int>( std::unexpect, 5 )));
        co_return 6;
    };

    auto result = co_await lambda2();
    EXPECT_EQ(result, (std::expected<long, int>(6)));
}

}