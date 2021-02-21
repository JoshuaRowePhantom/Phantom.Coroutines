#include "Phantom.Coroutines/detail/type_traits.h"
#include <tuple>
#include <type_traits>

namespace Phantom::Coroutines::detail
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

}

static_assert(false == is_in_types<int>);
static_assert(true == is_in_types<int, int>);
static_assert(false == is_in_types<int, bool>);
static_assert(true == is_in_types<int, int, bool>);
static_assert(true == is_in_types<int, bool, int>);
static_assert(true == is_in_types<int, int, int>);
static_assert(false == is_in_types<int, bool, bool>);

static_assert(std::is_same_v<int, enable_if_in_types_t<int, int>>);
static_assert(std::is_same_v<int, enable_if_in_types_t<int, int, bool>>);
static_assert(std::is_same_v<int, enable_if_in_types_t<int, bool, int>>);

// Test that enable_if_in_types_works_v returns true if the enable_if_in_types_t is found.
static_assert(enable_if_in_types_works_v<int, int>);
static_assert(enable_if_in_types_works_v<int, int, bool>);

// Now verify that enable_if_in_types doesn't produce a result in these cases.
static_assert(!enable_if_in_types_works_v<int, bool>);
static_assert(!enable_if_in_types_works_v<int>);

}