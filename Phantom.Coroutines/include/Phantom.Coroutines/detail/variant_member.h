namespace Phantom::Coroutines::detail
{

template<
    typename TDiscriminant,
    TDiscriminant Discriminant
> struct discriminant_tag {};

template<
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
        Discriminant discriminant
    ) const
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
        new[value] TValue(
            std::forward<TArgs>(args)...
        );
    }

    static bool destroy(
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

template<
    typename TDiscriminant,
    TDiscriminant Discriminant
> struct discriminant_tag {};

constexpr get_variant_holder_type(
    std::tuple<>
)
{

}

template<
    typename ... TVariants
> class variant_holder;

template<
> class variant_holder<
>
{
protected:
    typedef variant_holder<TVariants...>::holder_type holder_type;
};

template<
    typename ... TVariants
> class variant_holder<
    void,
    TVariants...
>
{
protected:
    typedef variant_holder<TVariants...>::holder_type holder_type;
};

}