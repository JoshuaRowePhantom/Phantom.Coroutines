#pragma once

#include <tuple>
#include <type_traits>
#include "coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{
// Determine if a given type is in a list of other types.
template<
    typename T,
    typename...TTypes
> constexpr bool is_in_types_v = (std::is_same_v<T, TTypes> || ...);

template<
    typename T,
    typename...TTypes
> constexpr bool is_not_in_types_v = !is_in_types_v<T, TTypes...>;

template<
    typename T,
    typename...TTypes
> using enable_if_in_types = std::enable_if<
    is_in_types_v<T, TTypes...>,
    T>;

template<
    typename T,
    typename...Types
>
using enable_if_in_types_t = typename enable_if_in_types<T, Types...>::type;

template<
    typename T
> concept Label =
std::is_empty_v<T>;

template<
    template<typename> typename Filter,
    typename TypesTuple,
    typename FilteredTypesTuple = std::tuple<>
> struct filter_tuple_types;

template<
    template<typename> typename Filter,
    typename FilteredTypesTuple
> struct filter_tuple_types<
    Filter,
    std::tuple<>,
    FilteredTypesTuple
>
{
    typedef FilteredTypesTuple tuple_type;
};

template<
    template<typename> typename Filter,
    typename Type,
    typename... RemainingTypes,
    typename... FilteredTypes
> struct filter_tuple_types<
    Filter,
    std::tuple<Type, RemainingTypes...>,
    std::tuple<FilteredTypes...>>
    :
    public std::conditional_t<
    Filter<Type>::value,
    filter_tuple_types<Filter, std::tuple<RemainingTypes...>, std::tuple<FilteredTypes..., Type>>,
    filter_tuple_types<Filter, std::tuple<RemainingTypes...>, std::tuple<FilteredTypes...>>
    >
{
};

template<
    template<typename> typename Filter,
    typename...Types
> struct filter_types
{
    typedef typename filter_tuple_types<Filter, std::tuple<Types...>, std::tuple<>>::tuple_type tuple_type;
};

// Determine if a tuple contains a given element type.
template<
    typename Type,
    typename Tuple
>
constexpr bool tuple_has_element_v = false;

template<
    typename Type,
    typename ... RemainingElements
>
constexpr bool tuple_has_element_v<
    Type,
    std::tuple<Type, RemainingElements...>>
    = true;

template<
    typename Type,
    typename OtherType,
    typename ... RemainingElements
>
constexpr bool tuple_has_element_v<
    Type,
    std::tuple<OtherType, RemainingElements...>>
    = tuple_has_element_v<Type, std::tuple<RemainingElements...>>;

template<
    typename BoundType
> struct same_as_filter
{
    template<
        typename Type
    > using filter = std::is_same<BoundType, Type>;
};

// Locate the index of a Type in a Tuple,
// returning no valid index if the type is not present or is duplicated.
template<
    typename Type,
    typename Tuple,
    typename = void
>
struct tuple_element_index;

template<
    typename Type,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<Type, RemainingTypes...>,
    std::enable_if_t<tuple_has_element_v<Type, std::tuple<RemainingTypes...>>>
>
{
};

template<
    typename Type,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<Type, RemainingTypes...>,
    std::enable_if_t<!tuple_has_element_v<Type, std::tuple<RemainingTypes...>>>
>
{
    static const size_t value = 0;
};

template<
    typename Type,
    typename OtherType,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<OtherType, RemainingTypes...>,
    std::void_t<
        std::enable_if_t<!std::is_same_v<Type, OtherType>>,
        decltype(tuple_element_index<Type, std::tuple<RemainingTypes...>>::value)>
>
{
    static const size_t value =
        1
        +
        tuple_element_index<Type, std::tuple<RemainingTypes...>>::value;
};

template<
    typename Type,
    typename Tuple
> constexpr size_t tuple_element_index_v = tuple_element_index<Type, Tuple>::value;


template<
    typename TAwaiter
>
concept is_awaiter =
requires (
    TAwaiter awaiter)
{
    { awaiter.await_ready() } -> std::same_as<bool>;
    { awaiter.await_resume() };
}
&&
(
    requires (
        TAwaiter awaiter,
        coroutine_handle<> continuation
        )
{
    { awaiter.await_suspend(continuation) } -> std::same_as<void>;
}
||
requires (
    TAwaiter awaiter,
    coroutine_handle<> continuation
    )
{
    { awaiter.await_suspend(continuation) } -> std::same_as<bool>;
}
||
requires (
    TAwaiter awaiter,
    coroutine_handle<> continuation
    )
{
    { awaiter.await_suspend(continuation) } -> std::convertible_to<coroutine_handle<>>;
}
)
;

template<
    typename TAwaitable
> concept has_co_await = requires(
    TAwaitable awaitable
    )
{
    requires is_awaiter<decltype(awaitable.operator co_await())>;
};

template<
    typename TAwaitable
> concept is_awaitable =
has_co_await<TAwaitable>
||
is_awaiter<TAwaitable>;

template<
    is_awaitable TAwaitable
>
decltype(auto) get_awaitable_result(
    TAwaitable&& awaitable
)
{
    if constexpr (has_co_await<TAwaitable>)
    {
        return (awaitable.operator co_await().await_resume());
    }
    else
    {
        return (awaitable.await_resume());
    }
}

template<
    has_co_await TAwaitable
>
decltype(auto) get_awaiter(
    TAwaitable&& awaitable
)
{
    return (awaitable.operator co_await());
}

template<
    is_awaiter TAwaitable
>
decltype(auto) get_awaiter(
    TAwaitable&& awaitable
)
{
    return (awaitable);
}

template<
    is_awaitable TAwaitable
>
struct awaitable_result_type
{
    typedef decltype((get_awaitable_result(std::declval<TAwaitable>()))) type;
};

template<
    is_awaitable TAwaitable
>
using awaitable_result_type_t = typename awaitable_result_type<TAwaitable>::type;

} // namespace detail

using detail::awaitable_result_type_t;
using detail::awaitable_result_type;
using detail::is_awaitable;
using detail::is_awaiter;
using detail::has_co_await;

} // namespace Phantom::Coroutines
