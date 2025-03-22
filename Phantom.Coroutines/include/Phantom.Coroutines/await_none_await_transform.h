#ifndef PHANTOM_COROUTINES_INCLUDE_AWAIT_NONE_AWAIT_TRANSFORM_H
#define PHANTOM_COROUTINES_INCLUDE_AWAIT_NONE_AWAIT_TRANSFORM_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "type_traits.h"
#else
import Phantom.Coroutines.type_traits;
#endif

namespace Phantom::Coroutines
{
namespace detail
{
// This utility class can be used by a promise type
// to disable co_await on all inherently awaitable types.
class await_none_await_transform
{
public:
    template<
        is_awaitable T
    > T&& await_transform(
        T&& t
    ) = delete;
};
}
using detail::await_none_await_transform;

}
#endif
