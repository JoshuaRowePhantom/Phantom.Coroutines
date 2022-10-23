#include <gtest/gtest.h>
#include "Phantom.Coroutines/detail/type_traits.h"
#include <tuple>
#include <type_traits>
#include "awaiters.h"

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

// Verify that awaitable_result_type_t produces valid results
static_assert(is_awaiter<typed_awaiter<void>>);
static_assert(is_awaiter<typed_awaiter<void, bool>>);
static_assert(is_awaiter<typed_awaiter<void, void>>);
static_assert(is_awaiter<typed_awaiter<void, coroutine_handle<>>>);
static_assert(is_awaiter<typed_awaiter<void, coroutine_handle<int>>>);
static_assert(!is_awaiter<typed_awaiter<void, void*>>);
static_assert(is_awaiter<typed_awaiter<int>>);
static_assert(is_awaiter<typed_awaiter<int&>>);
static_assert(is_awaiter<typed_awaiter<int&&>>);
static_assert(!is_awaiter<not_awaitable>);

static_assert(has_co_await_member<typed_awaitable<void>>);
static_assert(!has_co_await_member<not_awaitable>);

static_assert(std::same_as<typed_awaiter<void>, awaiter_type<typed_awaiter<void>>>);
static_assert(std::same_as<typed_awaiter<int>, awaiter_type<typed_awaiter<int>>>);
static_assert(std::same_as<typed_awaiter<int&>, awaiter_type<typed_awaiter<int&>>>);
static_assert(std::same_as<typed_awaiter<int&&>, awaiter_type<typed_awaiter<int&&>>>);

static_assert(std::same_as<typed_awaiter<void>&, awaiter_type<typed_awaiter<void>&>>);
static_assert(std::same_as<typed_awaiter<int>&, awaiter_type<typed_awaiter<int>&>>);
static_assert(std::same_as<typed_awaiter<int&>&, awaiter_type<typed_awaiter<int&>&>>);
static_assert(std::same_as<typed_awaiter<int&&>&, awaiter_type<typed_awaiter<int&&>&>>);

static_assert(std::same_as<typed_awaiter<void>, awaiter_type<typed_awaiter<void>&&>>);
static_assert(std::same_as<typed_awaiter<int>, awaiter_type<typed_awaiter<int>&&>>);
static_assert(std::same_as<typed_awaiter<int&>, awaiter_type<typed_awaiter<int&>&&>>);
static_assert(std::same_as<typed_awaiter<int&&>, awaiter_type<typed_awaiter<int&&>&&>>);

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

TEST(type_traits_test, get_awaiter_returns_awaiter_lvalue_as_itself)
{
    generic_awaiter<> awaiter;
    decltype(auto) result = get_awaiter(awaiter);
    static_assert(std::same_as<generic_awaiter<>&, decltype(result)>);
    ASSERT_EQ(&result, &awaiter);
}

TEST(type_traits_test, get_awaiter_returns_awaiter_rvalue_as_itself)
{
    generic_awaiter<> awaiter;
    decltype(auto) result = get_awaiter(std::move(awaiter));
    static_assert(std::same_as<generic_awaiter<>&&, decltype(result)>);
    ASSERT_EQ(&result, &awaiter);
}

TEST(type_traits_test, get_awaiter_returns_awaitable_lvalue_as_itself)
{
    generic_awaitable_lvalue<> awaitable;
    decltype(auto) result = get_awaiter(awaitable);
    static_assert(std::same_as<generic_awaiter<>&, decltype(awaitable.operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>&, decltype(result)>);
    ASSERT_EQ(&result, &awaitable.m_awaiter);
}

TEST(type_traits_test, get_awaiter_returns_awaitable_rvalue_as_itself)
{
    generic_awaitable_rvalue<> awaitable;
    decltype(auto) result = get_awaiter(std::move(awaitable));
    static_assert(std::same_as<generic_awaiter<>&&, decltype(std::move(awaitable).operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>&&, decltype(result)>);
    ASSERT_EQ(&result, &awaitable.m_awaiter);
}

TEST(type_traits_test, get_awaiter_returns_awaitable_value_as_copy)
{
    generic_awaitable_value<> awaitable;
    decltype(auto) result = get_awaiter(std::move(awaitable));
    static_assert(std::same_as<generic_awaiter<>, decltype(std::move(awaitable).operator co_await())>);
    static_assert(std::same_as<generic_awaiter<>, decltype(result)>);
    ASSERT_NE(&result, &awaitable.m_awaiter);
}

}
