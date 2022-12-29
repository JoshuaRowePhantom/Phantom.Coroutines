#include "async_test.h"
#include "Phantom.Coroutines/early_termination_task.h"
#include "Phantom.Coroutines/error_condition_early_termination.h"
#include "Phantom.Coroutines/expected_early_termination.h"

namespace Phantom::Coroutines
{
namespace
{
template<
    typename Value
> using expected_int_early_termination_task =
early_termination_task<
    std::expected<Value, int>,
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
        expected_int_early_termination_task<void>,
        detail::basic_early_termination_task<
            detail::early_termination_promise_inheritor<
                detail::basic_early_termination_promise<
                    std::expected<void, int>,
                    std::coroutine_handle<>
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

ASYNC_TEST(expected_early_termination_test, Can_co_await_successful_value)
{
    auto lambda = [&]() -> expected_int_early_termination_task<void>
    {
        std::string result = co_await std::expected<std::string, int>("hello world");
        EXPECT_EQ(result, "hello world");
        co_return{};
    };

    auto result = co_await lambda().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>()));
}

ASYNC_TEST(expected_early_termination_test, Can_co_await_unsuccessful_value)
{
    auto lambda = [&]() -> expected_int_early_termination_task<void>
    {
        std::string result = co_await std::expected<std::string, int>(std::unexpect, 1);
        // We should not reach here.
        EXPECT_TRUE(false);
        co_return{};
    };

    auto result = co_await lambda().handle_errors();
    EXPECT_EQ(result, (std::expected<void, int>(std::unexpect, 1)));
}

}