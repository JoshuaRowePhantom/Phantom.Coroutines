#pragma once

#include <functional>

namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename Value
>
class thread_local_storage
{
	std::function<TValue()> m_initializer;

public:
	thread_local_storage(
		std::function<TValue()> initializer
	)
	Value& get();
	const Value& get() const;

};

}
}