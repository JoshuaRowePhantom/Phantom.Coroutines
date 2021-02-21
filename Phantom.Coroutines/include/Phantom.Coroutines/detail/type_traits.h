#pragma once

#include <tuple>
#include <type_traits>

namespace Phantom::Coroutines::detail
{

// Determine if a given type is in a list of other types.
template<
    typename T,
    typename...TTypes
> concept is_in_types = (std::is_same_v<T, TTypes> || ...);

template<
    typename T,
    typename...TTypes
> using enable_if_in_types = std::enable_if<
    is_in_types<T, TTypes...>,
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
    typename... FilteredTypes,
    typename Type,
    typename... RemainingTypes
> struct filter_tuple_types<Filter, std::tuple<FilteredTypes...>, std::tuple<Type, RemainingTypes...>>
    :
public std::conditional_t<
    Filter<Type>::value,
    filter_tuple_types<Filter, std::tuple<FilteredTypes..., Type>, std::tuple<RemainingTypes...>>,
    filter_tuple_types<Filter, std::tuple<FilteredTypes...>, std::tuple<RemainingTypes...>>
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

}
