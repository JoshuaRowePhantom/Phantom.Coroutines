#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once

#include <concepts>
#include <type_traits>
#include "config.h"
#include "immovable_object.h"
#endif

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
     std::invocable<> Lambda
>
class scope_guard
    :
private immovable_object
{
    Lambda m_lambda;
public:
    template<
        std::invocable<> TLambda
    >
    scope_guard(
        TLambda lambda
    ) : m_lambda { std::forward<TLambda>(lambda) }
    {}

    ~scope_guard()
    {
        m_lambda();
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    std::invocable<> Lambda
> scope_guard(Lambda)->scope_guard<std::remove_reference_t<Lambda>>;

}
}
