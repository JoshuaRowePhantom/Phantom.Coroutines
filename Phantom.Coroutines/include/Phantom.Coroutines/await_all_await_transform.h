#ifndef PHANTOM_COROUTINES_INCLUDE_AWAIT_ALL_AWAIT_TRANSFORM_H
#define PHANTOM_COROUTINES_INCLUDE_AWAIT_ALL_AWAIT_TRANSFORM_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{
// This utility class can be used by a promise type
// that declares an await_transform method to enable
// awaiting on all other types that are inherently awaitable.
class await_all_await_transform
{
public:
    template<
        is_awaitable T
    > T&& await_transform(
        T&& t
    )
    {
        return std::forward<T>(t);
    }
};
}
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::await_all_await_transform;

}
#endif
