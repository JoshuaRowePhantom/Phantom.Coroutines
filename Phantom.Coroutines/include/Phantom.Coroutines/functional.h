#ifndef PHANTOM_COROUTINES_INCLUDE_FUNCTIONAL_H
#define PHANTOM_COROUTINES_INCLUDE_FUNCTIONAL_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/config_macros.h"
#include <utility>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace detail
{
template<
    typename Function
>
struct composed_function_wrapper
{
    Function function;

    decltype(auto) operator()(auto&& ... args)
    {
        return std::invoke(
            function,
            std::forward<decltype(args)>(args)...);
    }
};
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Functions
>
struct composed_function
    :
    detail::composed_function_wrapper<Functions>...
{
    composed_function(
        auto&& ... functions
    ) :
        detail::composed_function_wrapper<Functions>{ std::forward<decltype(functions)>(functions) }...
    {}

    using detail::composed_function_wrapper<Functions>::operator()...;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Functions
>
composed_function(
    Functions&& ... functions
) -> composed_function<std::remove_reference_t<Functions>...>;

}
#endif // PHANTOM_COROUTINES_INCLUDE_FUNCTIONAL_H
