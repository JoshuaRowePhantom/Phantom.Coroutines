export module Phantom.Coroutines.storage_for;

import Phantom.Coroutines.immovable_object;
import <algorithm>;
import <type_traits>;

namespace Phantom::Coroutines
{

template<
    typename... TValues
>
struct storage_for_impl;

template<    
>
struct storage_for_impl<
>
{
};

template<
    typename T
> struct storage_for_key {};

template<
    typename TValue,
    typename... TValues
>
struct storage_for_impl<
    TValue,
    TValues...
>
{
    union
    {
        storage_for_impl<TValues...> m_otherStorages;
        TValue m_value;
    };

    template<
        typename ThisValue
    > ThisValue& as(
        storage_for_key<ThisValue> key = {}
    )
    {
        if constexpr (std::same_as<TValue, ThisValue>)
        {
            return m_value;
        }
        else
        {
            return m_otherStorages.as(
                key);
        }
    }

    template<
        typename ThisValue,
        typename... Args
    > ThisValue& emplace(
        storage_for_key<ThisValue> key,
        Args&&... args
    )
    {
        if constexpr (std::same_as<TValue, ThisValue>)
        {
            return *new (&m_value)TValue(std::forward<Args>(args)...);
        }
        else
        {
            return m_otherStorages.emplace(
                key,
                std::forward<Args>(args)...
            );
        }
    }

    template<
        typename ThisValue
    > void destroy(
        storage_for_key<ThisValue> key = {}
    )
    {
        if constexpr (std::same_as<TValue, ThisValue>)
        {
            this->m_value::~TValue();
        }
        else
        {
            return m_otherStorages.destroy(
                key
            );
        }
    }
};

export template<
    typename ... TValues
> struct storage_for
    :
public storage_for_impl<
    TValues
>...,
private immovable_object
{
};

}