import Phantom.Coroutines.async_generator;

namespace cppcoro
{
template<
	typename T
>
using async_generator = ::Phantom::Coroutines::async_generator<T>;
}
