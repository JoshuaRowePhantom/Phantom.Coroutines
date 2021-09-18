#pragma once

#include "atomic_state_variant.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TValue
> 
class single_consumer_promise;

template<
    typename ValuesTuple,
    typename ValuesIndexSequence = std::make_index_sequence<std::tuple_size_v<ValuesTuple>>
>
class promise_variant_implementation;

template<
    typename... Values,
    size_t... ValueIndexes
>
class promise_variant_implementation<
    std::tuple<Values...>,
    std::index_sequence<size_t, ValueIndexes...>
>
{
    typedef atomic_state_variant<
        SingletonStateVariant<
            promise_variant_state_label<ValueIndexes>,
            Values
        >...,
        StateSet<coroutine_handle>,
        State<promise_variant_empty_label>
    > atomic_state_variant_type;

    atomic_state_variant_type m_state;
};

template<
    typename... TValues
>
class promise<
    std::variant<TValues...>
>
{
    typedef atomic_state_variant<
        SingletonStateVariant<
public:
    template<
        typename ... TArguments
    > promise& emplace(
        TArguments...&& arguments
    )
    {
        return *this;
    }
};

template<
    typename TValue
>
class promise
    :
private promise<std::variant<TValue>>
{
public:
    template<
        typename ... TArguments
    > promise& emplace(
        TArguments...&& arguments
    )
    {
        return *this;
    }
};

}

using detail::promise;
}
