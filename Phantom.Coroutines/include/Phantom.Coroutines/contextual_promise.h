#include "detail/coroutine.h"
#include "type_traits.h"
#include "detail/awaiter_wrapper.h"

namespace Phantom::Coroutines
{
namespace detail
{
template<
	typename Traits
> concept contextual_promise_traits = requires
{
	typename Traits::base_promise_type;
};

template<
	contextual_promise_traits Traits
> class contextual_promise
	:
public Traits::base_promise_type
{
	typedef Traits::base_promise_type base_promise_type;

	template<
		is_awaitable Awaiter
	>
	class base_restore_context_awaiter
		:
	private awaiter_wrapper<Awaiter>
	{
		Awaiter m_awaiter;

	protected:
		base_restore_context_awaiter(
			Awaiter&& awaiter
		) :
			m_awaiter(awaiter)
		{}

	public:

	};

	void enter()
	{

	}

	void leave()
	{

	}

	base_promise_type& base_promise();

public:
	auto initial_suspend() const noexcept(noexcept(base_promise().initial_suspend()))
	{

	}

	template<
		typename TAwaitable
	> auto await_transform(
		TAwaitable&& awaitable
	) const noexcept
	{}

	auto final_suspend() const noexcept(noexcept(base_promise().final_suspend()))
	{

	}
};

}
}