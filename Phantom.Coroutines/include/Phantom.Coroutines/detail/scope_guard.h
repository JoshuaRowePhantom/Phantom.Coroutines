#pragma once

#include <concepts>
#include <type_traits>
#include "immovable_object.h"

namespace Phantom::Coroutines
{
namespace detail
{

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

template<
	std::invocable<> Lambda
> scope_guard(Lambda)->scope_guard<std::remove_reference_t<Lambda>>;

}
}
