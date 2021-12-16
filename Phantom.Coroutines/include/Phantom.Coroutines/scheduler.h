#pragma once
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename T
> concept scheduler = is_awaitable<T>;

}
}