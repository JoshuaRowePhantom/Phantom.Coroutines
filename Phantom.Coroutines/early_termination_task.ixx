export module Phantom.Coroutines.early_termination_task;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.type_traits;
import <concepts>;
import <exception>;

namespace Phantom::Coroutines
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
export template<
	typename Traits
> class basic_early_termination_task
{

};

export template<
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

template<
	typename T
> concept is_early_termination_result =
is_template_instantiation<T, early_termination_result>;

// An early_termination_task converts exceptions and
// special returns into an early termination of the current coroutine
// and a resumption of an error-handling coroutine.
// If the caller was not an early_termination_task,
// the exception or special return is converted back into
// a rethrown exception in that caller.
// The underlying exception of a called can be obtained
// from an early_termination_task coroutine by using
// the handle_error() function.
export template<
	typename Traits
> class basic_early_termination_promise
{
public:
	coroutine_handle<> resume() noexcept
	{

	}

	void unhandled_exception() noexcept
	{
		set_result(
			early_termination_result
			{
				std::current_exception()
			}
		);
	}
};

export template<
	typename Promise
> concept is_basic_early_termination_promise
= is_template_instantiation<Promise, basic_early_termination_promise>;

export template<
	typename Transformer,
	typename Promise
> concept is_basic_early_termination_await_transformer
= std::convertible_to<Transformer, Promise>
&&
is_basic_early_termination_promise<Promise>;

export template<
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
	) noexcept
		: m_promise(static_cast<Promise&>(transformer))
	{
	}

	template<
		typename T
	> void set_result(
		T&& result
	) noexcept(std::is_nothrow_move_constructible_v<T>)
	{
		return m_promise.set_result(
			std::forward<T>(result)
		);
	}

	coroutine_handle<> resume() noexcept
	{
		return m_promise.resume();
	}
};

export template<
	is_basic_early_termination_promise Promise
> class basic_early_termination_await_transformer
{
public:
	template<
		typename T
	> decltype(auto) await_transform(
		T&& awaitable
	)
	{

	}
};

}