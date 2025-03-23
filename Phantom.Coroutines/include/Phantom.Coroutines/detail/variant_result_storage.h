#ifndef PHANTOM_COROUTINES_INCLUDE_VARIANT_RESULT_STORAGE_H
#define PHANTOM_COROUTINES_INCLUDE_VARIANT_RESULT_STORAGE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <type_traits>
#include <variant>
#include "Phantom.Coroutines/type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::detail
{
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> struct variant_return_result
{
    void return_value(
        this auto& self,
        T& value
    )
    {
        static_assert(!std::is_rvalue_reference_v<T>, "Cannot convert T& to T&&.");
        if constexpr (std::is_lvalue_reference_v<T>)
        {
            return self.return_variant_result(
                std::reference_wrapper(value));
        }
        else
        {
            return self.return_variant_result(
                value);
        }
    }

    void return_value(
        this auto& self,
        std::remove_reference_t<T>&& value
    )
    {
        static_assert(!std::is_lvalue_reference_v<T>, "Cannot convert T&& to T&.");
        if constexpr (std::is_rvalue_reference_v<T>)
        {
            return self.return_variant_result(
                std::reference_wrapper(value));
        }
        else
        {
            return self.return_variant_result(
                std::move(value));
        }
    }

    void return_value(
        this auto& self,
        auto&& value
    )
        requires (!std::same_as<T&, decltype(value)&>)
    {
        return self.return_variant_result(
            std::forward<decltype(value)>(value)
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

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> struct variant_result_storage
{
    typedef T result_type;
    typedef T& get_result_type;

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
    > static decltype(auto) resume_variant_result(
        Variant&& variant
    )
    {
        return std::get<Index>(
            std::forward<Variant>(variant));
    }
};

template<
> struct variant_result_storage<
    void
>
{
    typedef void result_type;
    typedef void get_result_type;

    static constexpr bool is_void = true;
    static constexpr bool is_reference = false;
    static constexpr bool is_lvalue_reference = false;
    static constexpr bool is_rvalue_reference = false;
    typedef std::monostate result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static void get_result(
        Variant&
    )
    {
        return;
    }

    template<
        size_t Index,
        typename Variant
    > static void resume_variant_result(
        Variant&&
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

    static constexpr bool is_void = false;
    static constexpr bool is_reference = true;
    static constexpr bool is_lvalue_reference = true;
    static constexpr bool is_rvalue_reference = false;
    typedef std::reference_wrapper<T> result_variant_member_type;

    template<
        size_t Index,
        typename Variant
    > static T& get_result(
        Variant&& variant
    )
    {
        return std::get<Index>(variant).get();
    }

    template<
        size_t Index,
        typename Variant
    > static T& resume_variant_result(
        Variant&& variant
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
    > static T&& resume_variant_result(
        Variant&& variant
    )
    {
        return std::move(std::get<Index>(variant).get());
    }
};

}
#endif
