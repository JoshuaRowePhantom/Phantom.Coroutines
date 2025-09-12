#ifndef PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#define PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <tuple>
#include <type_traits>
#include "detail/config_macros.h"
#endif

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Function
>
struct function_traits
{
    static_assert(std::is_function_v<Function>);
};

// Handle pointers to functions
template<
    typename Function
>
struct function_traits<
    Function*
> : 
function_traits<
    Function
>
{
    static constexpr bool is_function_pointer = true;
};

// Handle member functions.
template<
    typename ClassType,
    typename FunctionType
>
struct function_traits<
    FunctionType ClassType::*
> : function_traits<
    FunctionType
>
{
    static constexpr bool is_member_function_pointer = true;
};

// Now handle all the variations of functions
// We need each combination of cv and ref-qualifiers and noexcept qualifiers
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VALUE_ false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VALUE_const true
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VALUE_ false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VALUE_volatile true
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VALUE_ false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VALUE_noexcept true
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_REF_TOKEN_none
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_REF_TOKEN_lvalue &
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_REF_TOKEN_rvalue &&
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_LVALUE_REF_QUALIFIED_VALUE_none false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_LVALUE_REF_QUALIFIED_VALUE_lvalue true
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_LVALUE_REF_QUALIFIED_VALUE_rvalue false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_RVALUE_REF_QUALIFIED_VALUE_none false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_RVALUE_REF_QUALIFIED_VALUE_lvalue false
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_RVALUE_REF_QUALIFIED_VALUE_rvalue true

#define PHANTOM_COROUTINE_FUNCTION_TRAITS_VARIATION(const_keyword, volatile_keyword, noexcept_keyword, ref_token) \
    template< \
        typename ReturnType, \
        typename... Args \
    > struct function_traits< \
        ReturnType (Args...) const_keyword volatile_keyword PHANTOM_COROUTINE_FUNCTION_TRAITS_REF_TOKEN_##ref_token noexcept_keyword \
    > \
    { \
        using return_type = ReturnType; \
        using arguments_tuple_type = std::tuple<Args...>; \
        static constexpr size_t arity = sizeof...(Args); \
        template<size_t Index> \
        requires (Index < arity) \
        using argument_type = typename std::tuple_element<Index, arguments_tuple_type>::type; \
        static constexpr bool is_const = PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VALUE_##const_keyword; \
        static constexpr bool is_volatile = PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VALUE_##volatile_keyword; \
        static constexpr bool is_noexcept = PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VALUE_##noexcept_keyword; \
        static constexpr bool is_lvalue_ref_qualified = PHANTOM_COROUTINE_FUNCTION_TRAITS_LVALUE_REF_QUALIFIED_VALUE_##ref_token; \
        static constexpr bool is_rvalue_ref_qualified = PHANTOM_COROUTINE_FUNCTION_TRAITS_RVALUE_REF_QUALIFIED_VALUE_##ref_token; \
        static constexpr bool is_function_pointer = false; \
        static constexpr bool is_member_function_pointer = false; \
};

#define PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VARIATIONS(volatile_keyword, noexcept_keyword, ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_VARIATION(, volatile_keyword, noexcept_keyword, ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_VARIATION(const, volatile_keyword, noexcept_keyword, ref_token)
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VARIATIONS(noexcept_keyword, ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VARIATIONS(, noexcept_keyword, ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_CONST_VARIATIONS(volatile, noexcept_keyword, ref_token)
#define PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VARIATIONS(ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VARIATIONS(, ref_token) \
    PHANTOM_COROUTINE_FUNCTION_TRAITS_VOLATILE_VARIATIONS(noexcept, ref_token)

PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VARIATIONS(none)
PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VARIATIONS(lvalue)
PHANTOM_COROUTINE_FUNCTION_TRAITS_NOEXCEPT_VARIATIONS(rvalue)

}
#endif