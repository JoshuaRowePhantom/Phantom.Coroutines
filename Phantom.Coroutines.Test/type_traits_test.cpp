#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/config_macros.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.value_awaiter;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/type_traits.h"
#include "Phantom.Coroutines/value_awaiter.h"
#endif
#include <tuple>
#include <type_traits>
#include "detail/awaiters.h"

PHANTOM_COROUTINES_PUSH_DISABLE_INTERNAL_LINKAGE_WARNING()

namespace Phantom::Coroutines::detail
{

namespace
{
static_assert(false == is_in_types<int>);
static_assert(true == is_in_types<int, int>);
static_assert(false == is_in_types<int, bool>);
static_assert(true == is_in_types<int, int, bool>);
static_assert(true == is_in_types<int, bool, int>);
static_assert(true == is_in_types<int, int, int>);
static_assert(false == is_in_types<int, bool, bool>);

static_assert(true == is_template_instantiation<std::tuple<>, std::tuple>);
static_assert(true == is_template_instantiation<std::tuple<>&, std::tuple>);
static_assert(true == is_template_instantiation<const std::tuple<>&, std::tuple>);
static_assert(true == is_template_instantiation<std::tuple<>&&, std::tuple>);
static_assert(true == is_template_instantiation<const std::tuple<>&&, std::tuple>);
static_assert(false == is_template_instantiation<int, std::tuple>);

static_assert(!has_return_void<std::tuple<>>);
static_assert(!has_await_suspend<std::tuple<>>);
static_assert(!has_await_suspend<std::tuple<>&>);
static_assert(!has_await_suspend<std::tuple<>&&>);
static_assert(!has_yield_value<std::tuple<>>);

struct has_tested_members
{
    void await_suspend();
    void return_void();
    void yield_value();
};

static_assert(has_return_void<has_tested_members>);
static_assert(has_await_suspend<has_tested_members>);
static_assert(has_yield_value<has_tested_members>);

// Verify that filter_tuple_types works
template<
    typename T
> struct FilterTupleTypesTestFilter : std::bool_constant<
    std::is_same_v<T, int>
    || std::is_same_v<T, bool>>
{};

static_assert(std::is_same_v<
    std::tuple<>,
    typename filter_tuple_types<FilterTupleTypesTestFilter, std::tuple<>>::tuple_type
>);

static_assert(std::is_same_v<
    std::tuple<int, int, bool>,
    typename filter_tuple_types<FilterTupleTypesTestFilter, std::tuple<char, int, double, struct foo, int, float, bool>>::tuple_type
>);

struct test_coroutine_function_traits_task
{
};

struct get_promise
{
};

template<
    typename ... Args
>
struct test_coroutine_function_traits_promise
{
    std::suspend_always initial_suspend();
    std::suspend_always final_suspend() noexcept;
    void return_void();
    void unhandled_exception();
    test_coroutine_function_traits_task get_return_object();
    
    value_awaiter<test_coroutine_function_traits_promise&> await_transform(get_promise);

    using arguments_tuple_type = std::tuple<Args...>;
};

}
}

namespace std
{
template<
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::detail::test_coroutine_function_traits_task,
    Args...
>
{
    using promise_type = Phantom::Coroutines::detail::test_coroutine_function_traits_promise<Args...>;
};
}

namespace Phantom::Coroutines::detail
{
namespace
{
static_assert(std::same_as<
    std::coroutine_traits<test_coroutine_function_traits_task>,
    coroutine_function_traits<test_coroutine_function_traits_task()>::coroutine_traits_type
>);

static_assert(std::same_as<
    test_coroutine_function_traits_promise<>, 
    coroutine_function_traits<test_coroutine_function_traits_task()>::promise_type
>);

test_coroutine_function_traits_task test_coroutine_function_traits_free_function(int)
{
    auto& promise = co_await get_promise{};
    static_assert(std::same_as<test_coroutine_function_traits_promise<int>&, decltype(promise)>);
}

struct test_coroutine_function_traits_structure
{
    test_coroutine_function_traits_task test_coroutine_function_traits_member_function(int) const
    {
        auto& promise = co_await get_promise{};
        static_assert(std::same_as<test_coroutine_function_traits_promise<const test_coroutine_function_traits_structure &, int>&, decltype(promise)>);
    }

    template<typename Value>
    void verify_test_coroutine_function_traits_capturing_lambda(Value value) const;

    auto test_coroutine_function_traits_capturing_lambda() const
    {
        auto lambda = [&]<typename Lambda>(const Lambda&) -> test_coroutine_function_traits_task
        {
            auto& promise = co_await get_promise{};
            using arguments_tuple_type = typename std::remove_cvref_t<decltype(promise)>::arguments_tuple_type;
            static_assert(std::tuple_size_v<arguments_tuple_type> == 2);
            static_assert(std::same_as<const Lambda&, std::tuple_element_t<0, arguments_tuple_type>>);
            static_assert(std::same_as<const Lambda&, std::tuple_element_t<1, arguments_tuple_type>>);
        };
        lambda(lambda);
    }

};

template<typename Value>
void test_coroutine_function_traits_structure::verify_test_coroutine_function_traits_capturing_lambda(Value value) const
{
    static_assert(std::same_as<const decltype(value)&, decltype(test_coroutine_function_traits_capturing_lambda())>);
}

auto test_coroutine_function_traits_lambda = [](
    this auto& self,
    int
) -> test_coroutine_function_traits_task
{
    auto& promise = co_await get_promise{};
    static_assert(std::same_as<test_coroutine_function_traits_promise<long long>&, decltype(promise)>);
};
static_assert(std::same_as<test_coroutine_function_traits_task, decltype(test_coroutine_function_traits_lambda(0))>);

}


// Verify that tuple_has_element_v works
static_assert(false == tuple_has_element_v<int, std::tuple<>>);
static_assert(false == tuple_has_element_v<int, std::tuple<char>>);
static_assert(true == tuple_has_element_v<int, std::tuple<int>>);
static_assert(false == tuple_has_element_v<int, std::tuple<char, char>>);
static_assert(true == tuple_has_element_v<int, std::tuple<char, int>>);
static_assert(true == tuple_has_element_v<int, std::tuple<int, char>>);
static_assert(true == tuple_has_element_v<int, std::tuple<int, int>>);

// Used to test tuple_element_index
template<
    typename Type,
    typename Tuple,
    typename = void
> constexpr bool tuple_element_index_works = false;

template<
    typename Type,
    typename Tuple
> constexpr bool tuple_element_index_works<
    Type,
    Tuple,
    std::void_t<decltype(tuple_element_index<Type, Tuple>::value)>
> = true;

// Verify that tuple_element_index_works can return true.
static_assert(tuple_element_index_works<int, std::tuple<int>>);

// Verify that tuple_element_index doesn't return a value in these cases
static_assert(!tuple_element_index_works<int, std::tuple<>>);
static_assert(!tuple_element_index_works<int, std::tuple<char>>);
static_assert(!tuple_element_index_works<int, std::tuple<int, int>>);
static_assert(!tuple_element_index_works<int, std::tuple<int, char, int>>);
static_assert(!tuple_element_index_works<int, std::tuple<char, int, int>>);
static_assert(!tuple_element_index_works<int, std::tuple<int, int, char>>);
static_assert(!tuple_element_index_works<int, std::tuple<int, int, int>>);

// Verify that tuple_element_index itself can return a value.
static_assert(0 == tuple_element_index_v<int, std::tuple<int>>);
static_assert(0 == tuple_element_index_v<int, std::tuple<int, char>>);
static_assert(1 == tuple_element_index_v<int, std::tuple<char, int>>);
static_assert(0 == tuple_element_index_v<int, std::tuple<int, char, char>>);
static_assert(1 == tuple_element_index_v<int, std::tuple<char, int, char>>);
static_assert(2 == tuple_element_index_v<int, std::tuple<char, char, int>>);

// Verify that tuple_cat_types works
static_assert(std::same_as<tuple_cat_types_t<>, std::tuple<>>);
static_assert(std::same_as<tuple_cat_types_t<std::tuple<>>, std::tuple<>>);
static_assert(std::same_as<tuple_cat_types_t<std::tuple<>, std::tuple<>>, std::tuple<>>);
static_assert(std::same_as<tuple_cat_types_t<std::tuple<int>, std::tuple<char>>, std::tuple<int, char>>);
static_assert(std::same_as<tuple_cat_types_t<std::tuple<int>, std::tuple<char>, std::tuple<long>>, std::tuple<int, char, long>>);
static_assert(std::same_as<tuple_cat_types_t<std::tuple<int>, std::tuple<char, float>, std::tuple<long>>, std::tuple<int, char, float, long>>);

// Verify that awaitable_result_type_t produces valid results
static_assert(is_awaiter<typed_awaiter<void>>);
static_assert(is_awaiter<typed_awaiter<void, bool>>);
static_assert(is_awaiter<typed_awaiter<void, void>>);
static_assert(is_awaiter<typed_awaiter<void, coroutine_handle<>>>);
static_assert(is_awaiter<typed_awaiter<void, coroutine_handle<int>>>);
static_assert(is_awaiter<typed_awaiter<int>>);
static_assert(is_awaiter<typed_awaiter<int&>>);
static_assert(is_awaiter<typed_awaiter<int&&>>);
static_assert(!is_awaiter<not_awaitable>);

static_assert(has_co_await_member<typed_awaitable<void>>);
static_assert(!has_co_await_member<not_awaitable>);

static_assert(!has_co_await_member<generic_awaitable_lvalue<>>);
static_assert(has_co_await_member<generic_awaitable_lvalue<>&>);
static_assert(!has_co_await_member<generic_awaitable_lvalue<>&&>);

static_assert(has_co_await_member<generic_awaitable_rvalue<>>);
static_assert(!has_co_await_member<generic_awaitable_rvalue<>&>);
static_assert(has_co_await_member<generic_awaitable_rvalue<>&&>);

static_assert(std::same_as<typed_awaiter<void>&&, awaiter_type<typed_awaiter<void>>>);
static_assert(std::same_as<typed_awaiter<int>&&, awaiter_type<typed_awaiter<int>>>);
static_assert(std::same_as<typed_awaiter<int&>&&, awaiter_type<typed_awaiter<int&>>>);
static_assert(std::same_as<typed_awaiter<int&&>&&, awaiter_type<typed_awaiter<int&&>>>);

static_assert(std::same_as<typed_awaiter<void>&, awaiter_type<typed_awaiter<void>&>>);
static_assert(std::same_as<typed_awaiter<int>&, awaiter_type<typed_awaiter<int>&>>);
static_assert(std::same_as<typed_awaiter<int&>&, awaiter_type<typed_awaiter<int&>&>>);
static_assert(std::same_as<typed_awaiter<int&&>&, awaiter_type<typed_awaiter<int&&>&>>);

static_assert(std::same_as<typed_awaiter<void>&&, awaiter_type<typed_awaiter<void>&&>>);
static_assert(std::same_as<typed_awaiter<int>&&, awaiter_type<typed_awaiter<int>&&>>);
static_assert(std::same_as<typed_awaiter<int&>&&, awaiter_type<typed_awaiter<int&>&&>>);
static_assert(std::same_as<typed_awaiter<int&&>&&, awaiter_type<typed_awaiter<int&&>&&>>);

static_assert(std::same_as<typed_awaiter<void>, awaiter_type<typed_awaitable<void>>>);
static_assert(std::same_as<typed_awaiter<int>, awaiter_type<typed_awaitable<int>>>);
static_assert(std::same_as<typed_awaiter<int&>, awaiter_type<typed_awaitable<int&>>>);
static_assert(std::same_as<typed_awaiter<int&&>, awaiter_type<typed_awaitable<int&&>>>);

static_assert(std::same_as<void, awaitable_result_type_t<typed_awaitable<void>>>);
static_assert(std::same_as<int, awaitable_result_type_t<typed_awaitable<int>>>);
static_assert(std::same_as<int&, awaitable_result_type_t<typed_awaitable<int&>>>);
static_assert(std::same_as<int&&, awaitable_result_type_t<typed_awaitable<int&&>>>);

static_assert(std::same_as<void, awaitable_result_type_t<typed_awaiter<void>>>);
static_assert(std::same_as<int, awaitable_result_type_t<typed_awaiter<int>>>);
static_assert(std::same_as<int&, awaitable_result_type_t<typed_awaiter<int&>>>);
static_assert(std::same_as<int&&, awaitable_result_type_t<typed_awaiter<int&&>>>);

static_assert(std::same_as<void, awaitable_result_type_t<typed_awaitable<void>>>);
static_assert(std::same_as<int, awaitable_result_type_t<typed_awaitable<int>>>);
static_assert(std::same_as<int&, awaitable_result_type_t<typed_awaitable<int&>>>);
static_assert(std::same_as<int&&, awaitable_result_type_t<typed_awaitable<int&&>>>);

// Verify that awaitable_result_t pays attention to the rvalue/lvalue-ness of the operand.
// Rvalue
static_assert(std::same_as<void, awaitable_result_type_t<typed_awaitable<void, void, void>>>);
static_assert(std::same_as<long, awaitable_result_type_t<typed_awaitable<int, void, long>>>);
static_assert(std::same_as<long&, awaitable_result_type_t<typed_awaitable<int&, void, long&>>>);
static_assert(std::same_as<long&&, awaitable_result_type_t<typed_awaitable<int&&, void, long&&>>>);

// Lvalue
static_assert(std::same_as<void, awaitable_result_type_t<typed_awaitable<void, void, void>&>>);
static_assert(std::same_as<int, awaitable_result_type_t<typed_awaitable<int, void, long>&>>);
static_assert(std::same_as<int&, awaitable_result_type_t<typed_awaitable<int&, void, long&>&>>);
static_assert(std::same_as<int&&, awaitable_result_type_t<typed_awaitable<int&&, void, long&&>&>>);

// Rvalue reference
static_assert(std::same_as<void, awaitable_result_type_t<typed_awaitable<void, void, void>&&>>);
static_assert(std::same_as<long, awaitable_result_type_t<typed_awaitable<int, void, long>&&>>);
static_assert(std::same_as<long&, awaitable_result_type_t<typed_awaitable<int&, void, long&>&&>>);
static_assert(std::same_as<long&&, awaitable_result_type_t<typed_awaitable<int&&, void, long&&>&&>>);

TEST(type_traits_test, get_awaiter_returns_awaiter_lvalue_as_lvalue_reference)
{
    generic_awaiter<> awaiter;
    decltype(auto) result = get_awaiter(awaiter);
    static_assert(std::same_as<generic_awaiter<>&, decltype(result)>);
    ASSERT_EQ(&result, &awaiter);
}

TEST(type_traits_test, get_awaiter_returns_awaiter_rvalue_reference_as_rvalue_reference)
{
    generic_awaiter<> awaiter;
    decltype(auto) result = get_awaiter(std::move(awaiter));
    static_assert(std::same_as<generic_awaiter<>&&, decltype(result)>);
    ASSERT_EQ(&result, &awaiter);
}

TEST(type_traits_test, get_awaiter_returns_co_await_value_reference_as_value)
{
    generic_awaitable_value<> awaitable;
    decltype(auto) result = get_awaiter(std::move(awaitable));
    static_assert(std::same_as<generic_awaiter<>, decltype(std::move(awaitable).operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>, decltype(result)>);
    ASSERT_NE(&result, &awaitable.m_awaiter);
}

TEST(type_traits_test, get_awaiter_returns_co_await_lvalue_reference_as_lvalue_reference)
{
    generic_awaitable_lvalue<> awaitable;
    decltype(auto) result = get_awaiter(awaitable);
    static_assert(std::same_as<generic_awaiter<>&, decltype(awaitable.operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>&, decltype(result)>);
    ASSERT_EQ(&result, &awaitable.m_awaiter);
}

TEST(type_traits_test, get_awaiter_returns_co_await_rvalue_reference_as_rvalue_reference)
{
    generic_awaitable_rvalue<> awaitable;
    decltype(auto) result = get_awaiter(std::move(awaitable));
    static_assert(std::same_as<generic_awaiter<>&&, decltype(std::move(awaitable).operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>&&, decltype(result)>);
    ASSERT_EQ(&result, &awaitable.m_awaiter);
}

template<
    typename Owner,
    typename Value,
    typename ExpectedResult
>
struct assert_forward_owned_expected_result
{
    assert_forward_owned_expected_result()
    {
        std::decay_t<Owner> ownerVariable;
        std::decay_t<Value> valueVariable;
        
        Owner owner = static_cast<Owner>(ownerVariable);
        Value value = static_cast<Value>(valueVariable);

        std::ignore = owner;

        using ActualResult = decltype(forward_owned<Owner, Value>(std::declval<Value>()));

        static_assert(std::same_as<ActualResult, ExpectedResult>);
        auto&& result = forward_owned<Owner, Value>(std::forward<Value>(value));
        EXPECT_EQ(&value, &result);
    }
};

TEST(forward_owned_test, return_types_are_correct)
{
    struct Owner {};
    struct Value {};
    assert_forward_owned_expected_result<Owner, Value, Value&&> {};
    assert_forward_owned_expected_result<Owner, Value&, Value&> {};
    assert_forward_owned_expected_result<Owner, Value&&, Value&&> {};
    assert_forward_owned_expected_result<Owner&, Value, Value&> {};
    assert_forward_owned_expected_result<Owner&, Value&, Value&> {};
    assert_forward_owned_expected_result<Owner&, Value&&, Value&&> {};
    assert_forward_owned_expected_result<Owner&&, Value, Value&&> {};
    assert_forward_owned_expected_result<Owner&&, Value&, Value&> {};
    assert_forward_owned_expected_result<Owner&&, Value&&, Value&&> {};
}

TEST(tuple_extract_convertible_elements, can_extract_by_reference)
{
    struct base {};
    struct derived : base {};
    struct not_derived {};

    base base1;
    base base2;
    const base const_base1;
    derived derived1;
    derived derived2;
    const derived const_derived1;
    not_derived not_derived1;
    not_derived not_derived2;
    const not_derived const_not_derived1;
    int int1;
    long long1;

    {
        auto tuple = std::tie(
            base1
        );
        auto result = tuple_extract_convertible_elements<base>(tuple);
        static_assert(std::same_as<std::tuple<base&>, decltype(result)>);

        ASSERT_EQ(&base1, &get<0>(result));
    }

    {
        auto tuple = std::tie(
            derived1
        );
        auto result = tuple_extract_convertible_elements<base&>(tuple);
        static_assert(std::same_as<std::tuple<derived&>, decltype(result)>);

        ASSERT_EQ(&derived1, &get<0>(result));
    }
    
    {
        auto tuple = std::tie(
            not_derived1
        );
        auto result = tuple_extract_convertible_elements<base&>(tuple);
        static_assert(std::same_as<std::tuple<>, decltype(result)>);
    }

    {
        auto tuple = std::tie(
            base1,
            derived1,
            not_derived1,
            base2,
            derived2,
            not_derived2
        );
        auto result = tuple_extract_convertible_elements<base&>(tuple);
        static_assert(std::same_as<std::tuple<base&, derived&, base&, derived&>, decltype(result)>);
        ASSERT_EQ(&base1, &get<0>(result));
        ASSERT_EQ(&derived1, &get<1>(result));
        ASSERT_EQ(&base2, &get<2>(result));
        ASSERT_EQ(&derived2, &get<3>(result));
    }

    {
        auto tuple = std::tie(
            int1,
            long1
        );
        auto result = tuple_extract_convertible_elements<base&>(tuple);
        static_assert(std::same_as<std::tuple<>, decltype(result)>);
    }

    {
        auto tuple = std::tie(
            int1,
            long1
        );
        auto result = tuple_extract_convertible_elements<int&>(tuple);
        static_assert(std::same_as<std::tuple<int&>, decltype(result)>);
        ASSERT_EQ(&int1, &get<0>(result));
    }

    {
        auto tuple = std::tie(
            int1,
            long1
        );
        auto result = tuple_extract_convertible_elements<long&>(tuple);
        static_assert(std::same_as<std::tuple<long&>, decltype(result)>);
        ASSERT_EQ(&long1, &get<0>(result));
    }

    {
        const auto tuple = std::tie(
            base1,
            derived1,
            not_derived1
        );
        auto result = tuple_extract_convertible_elements<base&>(tuple);
        static_assert(std::same_as<std::tuple<base&, derived&>, decltype(result)>);
        ASSERT_EQ(&base1, &get<0>(result));
        ASSERT_EQ(&derived1, &get<1>(result));
    }

    {
        const auto tuple = std::tie(
            base1,
            derived1,
            not_derived1
        );
        auto result = tuple_extract_convertible_elements<const base&>(tuple);
        static_assert(std::same_as<std::tuple<base&, derived&>, decltype(result)>);
        ASSERT_EQ(&base1, &get<0>(result));
        ASSERT_EQ(&derived1, &get<1>(result));
    }

    {
        auto tuple = std::tie(
            const_base1,
            const_derived1,
            const_not_derived1
        );
        auto result = tuple_extract_convertible_elements<const base&>(tuple);
        static_assert(std::same_as<std::tuple<const base&, const derived&>, decltype(result)>);
        ASSERT_EQ(&const_base1, &get<0>(result));
        ASSERT_EQ(&const_derived1, &get<1>(result));
    }
}

TEST(value_storage_test, can_default_construct)
{
    detail::value_storage<std::string> holder;
    ASSERT_EQ("", holder.value());
}

TEST(value_storage_test, can_construct_from_arguments)
{
    detail::value_storage<std::string> holder{ size_t(10), 'c' };
    ASSERT_EQ("cccccccccc", holder.value());
}

TEST(value_storage_test, can_construct_from_lambda)
{
    detail::value_storage<std::string> holder{ []() { return std::string("hello"); } };
    ASSERT_EQ("hello", holder.value());
}

TEST(value_storage_test, can_get_const_value)
{
    detail::value_storage<std::string> holder{ "hello" };
    ASSERT_EQ("hello", holder.value());
    const auto& constHolder = holder;
    ASSERT_EQ("hello", constHolder.value());
}

}

// Pop disabling internal linkage warnings
PHANTOM_COROUTINES_POP_WARNINGS()
