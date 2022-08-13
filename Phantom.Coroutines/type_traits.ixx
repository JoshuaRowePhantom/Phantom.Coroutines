export module Phantom.Coroutines.type_traits;

import Phantom.Coroutines.coroutine;
import <optional>;
import <tuple>;
import <type_traits>;

namespace Phantom::Coroutines
{
// Determine if a given type is an instantiation of a template
// accepting type arguments.
template<
    typename T,
    template <typename ...> typename Template
> constexpr bool is_template_instantiation_v = false;

template<
    typename... Args,
    template <typename ...> typename Template
> constexpr bool is_template_instantiation_v<
    Template<Args...>,
    Template
    > = true;

template<
    typename T,
    template <typename ...> typename Template
> concept is_template_instantiation = is_template_instantiation_v<T, Template>;

// Determine if a given type is in a list of other types.
export template<
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

export template<
    typename T,
    typename...Types
>
using enable_if_in_types_t = typename enable_if_in_types<T, Types...>::type;

template<
    typename T
> concept Label =
std::is_empty_v<T>;

export template<
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
export template<
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
export template<
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

export template<
    typename Type,
    typename Tuple
> constexpr size_t tuple_element_index_v = tuple_element_index<Type, Tuple>::value;

export template<
    typename TAwaiter
> concept has_void_await_suspend = requires (
    TAwaiter awaiter,
    coroutine_handle<> continuation)
{
    { awaiter.await_suspend(continuation) } -> std::same_as<void>;
};

export template<
    typename TAwaiter
> concept has_bool_await_suspend = requires (
    TAwaiter awaiter,
    coroutine_handle<> continuation)
{
    { awaiter.await_suspend(continuation) } -> std::same_as<bool>;
};

export template<
    typename TAwaiter
> concept has_symmetric_transfer_await_suspend = requires (
    TAwaiter awaiter,
    coroutine_handle<> continuation)
{
    { awaiter.await_suspend(continuation) } -> std::convertible_to<coroutine_handle<>>;
};

export template<
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
    has_void_await_suspend<TAwaiter>
||  has_bool_await_suspend<TAwaiter>
||  has_symmetric_transfer_await_suspend<TAwaiter>
)
;

export template<
    typename TAwaitable
> concept has_co_await = requires(
    TAwaitable awaitable
    )
{
    { awaitable.operator co_await() } -> is_awaiter;
};

export template<
    typename TAwaitable
> concept is_awaitable =
has_co_await<TAwaitable>
||
is_awaiter<TAwaitable>;

template<
    has_co_await TAwaitable
>
decltype(auto) get_awaiter(
    TAwaitable&& awaitable
)
{
    return std::forward<TAwaitable>(awaitable).operator co_await();
}

template<
    is_awaiter TAwaitable
>
decltype(auto) get_awaiter(
    TAwaitable&& awaitable
)
{
    return std::forward<TAwaitable>(awaitable);
}

template<
    typename T
> struct remove_rvalue_reference
{
    typedef T type;
};

template<
    typename T
> struct remove_rvalue_reference<T&&>
{
    typedef T type;
};

template<
    typename T
> using remove_rvalue_reference_t = typename remove_rvalue_reference<T>::type;

export template<
    typename Awaitable
> using awaiter_type = remove_rvalue_reference_t<decltype(get_awaiter(std::declval<Awaitable>()))>;

template<
    is_awaitable TAwaitable
>
decltype(auto) get_awaitable_result(
    TAwaitable&& awaitable
)
{
    return (get_awaiter(std::forward<TAwaitable>(awaitable)).await_resume());
}

template<
    is_awaitable TAwaitable
>
struct awaitable_result_type
{
    typedef decltype((get_awaitable_result(std::declval<TAwaitable>()))) type;
};

export template<
    is_awaitable TAwaitable
>
using awaitable_result_type_t = typename awaitable_result_type<TAwaitable>::type;

export template<
    typename T
> concept is_optional = is_template_instantiation<T, std::optional>;

} // namespace Phantom::Coroutines