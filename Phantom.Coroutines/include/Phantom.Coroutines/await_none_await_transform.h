#pragma once
#include "type_traits.h"

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