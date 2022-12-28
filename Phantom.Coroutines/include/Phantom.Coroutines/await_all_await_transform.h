#pragma once
#include "type_traits.h"

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
using detail::await_all_await_transform;

}