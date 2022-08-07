#include "detail/coroutine.h"
#include "type_traits.h"
#include "detail/awaiter_wrapper.h"

namespace Phantom::Coroutines
{
namespace detail
{
template<
	typename Traits
> concept contextual_promise_traits = true;

template<
	contextual_promise_traits Traits
> class contextual_promise
	:
public Traits::base_promise_type
{
	typedef Traits::base_promise_type base_promise_type;

	template<
		is_awaiter Awaiter
	>
	class base_restore_context_awaiter
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

public:
	auto initial_suspend() const noexcept(noexcept(base_promise_type::initial_suspend()))
	{

	}
};

}
}