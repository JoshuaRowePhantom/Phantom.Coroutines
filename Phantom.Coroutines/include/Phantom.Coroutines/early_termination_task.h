#include "detail/type_traits.h"
#include <concepts>

namespace Phantom::Coroutines
{
namespace detail
{

// An early_termination_task converts exceptions and
// special returns into an early termination of the current coroutine
// and a resumption of an error-handling coroutine.
// If the caller was not an early_termination_task,
// the exception or special return is converted back into
// a rethrown exception in that caller.
// The underlying exception of a called can be obtained
// from an early_termination_task coroutine by using
// the handle_error() function.
template<
	typename Traits
> class basic_early_termination_task
{

};

template<
	typename T
> class early_termination_result
{
	T m_value;
public:
	template<
		typename ... Args
	> early_termination_result(
		Args&&... args
	) :
		m_value(std::forward<Args>(args)...)
	{
	}
};

// An early_termination_task converts exceptions and
// special returns into an early termination of the current coroutine
// and a resumption of an error-handling coroutine.
// If the caller was not an early_termination_task,
// the exception or special return is converted back into
// a rethrown exception in that caller.
// The underlying exception of a called can be obtained
// from an early_termination_task coroutine by using
// the handle_error() function.
template<
	typename Traits
> class basic_early_termination_promise
{
public:
	void unhandled_exception()
	{
	}
};

template<
	typename Promise
> concept is_basic_early_termination_promise
= is_template_instantiation_v<Promise, basic_early_termination_promise>;

template<
	typename Transformer,
	is_basic_early_termination_promise Promise
> concept is_basic_early_termination_await_transformer
= std::convertible_to<Transformer, Promise>;

template<
	is_basic_early_termination_promise Promise
> class basic_early_termination_awaiter
{
	Promise& m_promise;
protected:
	template<
		is_basic_early_termination_await_transformer AwaitTransformer
	>
	basic_early_termination_awaiter(
		AwaitTransformer& transformer
	)
		: m_promise(static_cast<Promise&>(transformer))
	{
	}

	template<
		typename T
	> void set_result(
		early_termination_result<T>&& result);

	template<
		typename T
	> void set_result(
		const early_termination_result<T>& result);

	std::coroutine_handle<> resume() noexcept;
};

}
}