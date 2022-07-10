export module Phantom.Coroutines.scheduler;
import Phantom.Coroutines.type_traits;

namespace Phantom::Coroutines
{

export template<
	typename T
> concept is_scheduler = requires (T t)
{
	{ t.schedule() } -> is_awaitable;
};

}
