#pragma once
#include "atomic_state.h"


namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TValue
> class DiscriminatedUnionMember
{};

template<
    typename TDiscriminatedUnionMember
> constexpr bool IsDiscriminatedUnionMember = false;

template<
    typename TValue
> constexpr bool IsDiscriminatedUnionMember<
    DiscriminatedUnionMember<TValue> = true;

template<
    typename TDiscriminatedUnionMember
> concept DiscriminatedUnionMember
= IsDiscriminatedUnionMember<TDiscriminatedUnionMember>;

template<
    typename TDiscriminant,
    DiscriminatedUnionMember ... TDiscriminatedUnionMembers
> class DiscriminatedUnionMemberHandler;

template<
    typename TDiscriminant
>
class DiscriminatedUnionMemberHandler<
    TDiscriminant
>
{};

template<
    typename TDiscriminant,
    typename TValue,
    DiscriminatedUnionMember ... TDiscriminatedUnionMembers
> class DiscriminatedUnionMemberHandler<
    DiscriminatedUnionMember<TValue>,
    TDiscriminatedUnionMembers...
> :
    public DiscriminatedUnionMemberHandler<
        TDiscriminant,
        TDiscriminatedUnionMembers...
    >
{

};

//
//template<
//    typename TLabel,
//    typename TData
//> class SingletonStateVariant
//    :
//    public SingletonState<TLabel>
//{
//public:
//    using typename SingletonStateVariant::SingletonState::Label;
//    using SingletonStateVariant::SingletonState::is_singleton;
//    static constexpr bool is_variant = true;
//};
//
//template<
//    typename TStateType
//> constexpr bool IsStateVariantType = false;
//
//template<
//    typename TLabel,
//    typename TData
//> constexpr bool IsStateVariantType<
//    SingletonStateVariant<TLabel, TData>
//> = true;
//
//template<
//    typename TState
//> concept StateVariantType =
//StateType<TState>
//||
//IsStateVariantType<TState>;
//
//template<
//    typename TRepresentation,
//    StateVariantType... TStates
//> 
//class basic_atomic_state_variant
//{
//public:
//    void() {
//        std::atomic<int> i;
//        i.wait();
//    }
//};

}


}
