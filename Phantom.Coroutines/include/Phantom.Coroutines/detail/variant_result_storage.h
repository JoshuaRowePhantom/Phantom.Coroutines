#pragma once
#include <type_traits>
#include <variant>

namespace Phantom::Coroutines::detail
{
template<
    typename T
> struct variant_return_result
{
    void return_value(
        this auto& self,
        auto&& value
    )
    {
        return self.return_variant_result(
            std::forward<decltype(value)>(value)
        );
    }

    void return_value(
        this auto& self,
        std::monostate
    ) requires
        std::default_initializable<T>
    {
        return self.return_variant_result(
            T{}
        );
    }
};

template<
> struct variant_return_result<void>
{
    void return_void(
        this auto& self
    )
    {
        return self.return_variant_result(
            std::monostate{}
        );
    }
};

template<
    typename T
> struct variant_result_storage
{
    typedef T result_type;
    typedef T& get_result_type;
    typedef T&& return_result_type;

    static constexpr bool is_void = false;
    static constexpr bool is_reference = false;
    static constexpr bool is_lvalue_reference = false;
    static constexpr bool is_rvalue_reference = false;
    typedef T result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static get_result_type get_result(
        Variant& variant
    )
    {
        return std::get<Index>(variant);
    }

    template<
        size_t Index,
        typename Variant
    > static return_result_type return_result(
        Variant& variant
    )
    {
        return std::move(std::get<Index>(variant));
    }
};

template<
> struct variant_result_storage<
    void
>
{
    typedef void result_type;
    typedef void get_result_type;
    typedef void return_result_type;

    static constexpr bool is_void = true;
    static constexpr bool is_reference = false;
    static constexpr bool is_lvalue_reference = false;
    static constexpr bool is_rvalue_reference = false;
    typedef std::monostate result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static void get_result(
        Variant& variant
    )
    {
        return;
    }

    template<
        size_t Index,
        typename Variant
    > static void return_result(
        Variant& variant
    )
    {
        return;
    }
};

template<
    typename T
> struct variant_result_storage<
    T&
>
{
    typedef T& result_type;
    typedef T& get_result_type;
    typedef T& return_result_type;

    static constexpr bool is_void = false;
    static constexpr bool is_reference = true;
    static constexpr bool is_lvalue_reference = true;
    static constexpr bool is_rvalue_reference = false;
    typedef std::reference_wrapper<T> result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static T& get_result(
        Variant& variant
    )
    {
        return std::get<Index>(variant).get();
    }

    template<
        size_t Index,
        typename Variant
    > static T& return_result(
        Variant& variant
    )
    {
        return std::get<Index>(variant).get();
    }
};

template<
    typename T
> struct variant_result_storage<
    T&&
>
{
    typedef T&& result_type;
    typedef T&& get_result_type;
    typedef T&& return_result_type;

    static constexpr bool is_void = false;
    static constexpr bool is_reference = true;
    static constexpr bool is_lvalue_reference = false;
    static constexpr bool is_rvalue_reference = true;
    typedef std::reference_wrapper<T> result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static T&& get_result(
        Variant& variant
    )
    {
        return std::move(std::get<Index>(variant).get());
    }

    template<
        size_t Index,
        typename Variant
    > static T&& return_result(
        Variant& variant
    )
    {
        return std::move(std::get<Index>(variant).get());
    }
};

}