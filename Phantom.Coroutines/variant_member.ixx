export module Phantom.Coroutines.variant_member;

import <type_traits>;

namespace Phantom::Coroutines
{

export template<
    typename TDiscriminant,
    TDiscriminant Discriminant
> struct discriminant_tag {};

export template<
    typename TDiscriminant,
    TDiscriminant Discriminant,
    typename TValue
>
class variant_member
{
protected:
    typedef discriminant_tag<TDiscriminant, Discriminant> discriminant_tag;
    typedef TValue value_type;
    typedef TValue storage_type;
    const TDiscriminant discriminant = Discriminant;
    typedef TDiscriminant discriminant_type;

    static constexpr bool is_same_as(
        TDiscriminant discriminant
    )
    {
        return discriminant == Discriminant;
    }

    template<
        typename ... TArgs
    >
    static void create(
        discriminant_tag,
        void* value,
        TArgs&& ... args
    )
    {
        new(value) TValue(
            std::forward<TArgs>(args)...
        );
    }

    static bool destroy(
        discriminant_tag,
        TDiscriminant discriminant,
        void* value
    )
    {
        if (is_same_as(discriminant))
        {
            reinterpret_cast<TValue*>(value)->~TValue();
            return true;
        }
        return false;
    }
};

}