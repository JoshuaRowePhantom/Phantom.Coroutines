#pragma once

namespace Phantom::Coroutines::detail
{

template<
    typename T,
    typename...TTypes
> struct enable_if_in_types;

// This template matches if the type T is the first
// type in the list of types,
// and therefore successfully defines "type".
template<
    typename T,
    typename...TTypes
> struct enable_if_in_types<T, T, TTypes...>
{
    typedef T type;
};

// This template matches if the type T is NOT the first
// type in the list of types,
// and tries again on the remainder of the list.
template<
    typename T,
    typename TOther,
    typename...TTypes
> struct enable_if_in_types<T, TOther, TTypes...>
    : public enable_if_in_types<T, TTypes...>
{
};

// This template matches if the type list is empty,
// and represents a failure to match.  It does not
// define "type".
template<
    typename T
> struct enable_if_in_types<T>
{};

template<
    typename T,
    typename...Types
>
using enable_if_in_types_t = typename enable_if_in_types<T, Types...>::type;

}
