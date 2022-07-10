import Phantom.Coroutines.type_traits;
import <tuple>;
import <type_traits>;
import Phantom.Coroutines.Test.awaiters;

namespace Phantom::Coroutines
{

namespace
{
template<
    typename Tuple,
    typename = void
> constexpr bool enable_if_in_types_works_impl_v = false;

template<
    typename T,
    typename...Types
> constexpr bool enable_if_in_types_works_impl_v<
    std::tuple<T, Types...>,
    std::void_t<enable_if_in_types_t<T, Types...>>
> = true;

template<
    typename T,
    typename...Types
> constexpr bool enable_if_in_types_works_v =
enable_if_in_types_works_impl_v<
    std::tuple<T, Types...>
>;

static_assert(false == is_in_types_v<int>);
static_assert(true == is_in_types_v<int, int>);
static_assert(false == is_in_types_v<int, bool>);
static_assert(true == is_in_types_v<int, int, bool>);
static_assert(true == is_in_types_v<int, bool, int>);
static_assert(true == is_in_types_v<int, int, int>);
static_assert(false == is_in_types_v<int, bool, bool>);

static_assert(std::is_same_v<int, enable_if_in_types_t<int, int>>);
static_assert(std::is_same_v<int, enable_if_in_types_t<int, int, bool>>);
static_assert(std::is_same_v<int, enable_if_in_types_t<int, bool, int>>);

// Test that enable_if_in_types_works_v returns true if the enable_if_in_types_t is found.
static_assert(enable_if_in_types_works_v<int, int>);
static_assert(enable_if_in_types_works_v<int, int, bool>);

// Now verify that enable_if_in_types doesn't produce a result in these cases.
static_assert(!enable_if_in_types_works_v<int, bool>);
static_assert(!enable_if_in_types_works_v<int>);

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
//static_assert(!is_awaiter<typed_awaiter<void, void*>>);
static_assert(is_awaiter<typed_awaiter<int>>);
static_assert(is_awaiter<typed_awaiter<int&>>);
static_assert(is_awaiter<typed_awaiter<int&&>>);
static_assert(!is_awaiter<not_awaitable>);

static_assert(has_co_await<typed_awaitable<void>>);
static_assert(!has_co_await<not_awaitable>);

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

}
