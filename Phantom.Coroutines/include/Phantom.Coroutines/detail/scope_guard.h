#ifndef PHANTOM_COROUTINES_INCLUDE_SCOPE_GUARD_H
#define PHANTOM_COROUTINES_INCLUDE_SCOPE_GUARD_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <type_traits>
#include "config.h"
#include "immovable_object.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

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
#endif
