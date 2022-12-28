#pragma once
#include "Phantom.Coroutines/type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_awaitable Awaitable
> class awaiter_wrapper;

// The is_awaiter specialization provides the behavior of wrapping
// an actual awaiter object.
template<
	is_awaiter Awaiter
> class awaiter_wrapper<
	Awaiter
>
{
protected:
	typedef Awaiter awaiter_type;

private:
	// This will be the underlying awaiter type, either value, l-value reference, or r-value reference.
	awaiter_type m_awaiter;

public:
	explicit awaiter_wrapper(
		Awaiter awaiter
	) noexcept
		requires std::is_reference_v<Awaiter>
		: m_awaiter(std::forward<Awaiter>(awaiter))
	{}

	template<
		std::invocable AwaiterFunc
	>
	requires std::is_invocable_r_v<Awaiter, AwaiterFunc>
	explicit awaiter_wrapper(
		AwaiterFunc&& awaiterFunc
	) noexcept(noexcept(
		std::invoke(std::forward<decltype(awaiterFunc)>(awaiterFunc))
		))
		: m_awaiter
		{
			std::invoke(std::forward<decltype(awaiterFunc)>(awaiterFunc))
		}
	{}

	decltype(auto) await_ready(
		auto&&... args
	) noexcept(noexcept(awaiter().await_ready(std::forward<decltype(args)>(args)...)))
	{
		return awaiter().await_ready(
			std::forward<decltype(args)>(args)...
		);
	}

	decltype(auto) await_suspend(
		auto&&... args
	) noexcept(
		noexcept(awaiter().await_suspend(std::forward<decltype(args)>(args)...))
		)
	{
		return awaiter().await_suspend(std::forward<decltype(args)>(args)...);
	}

	decltype(auto) await_resume(
		auto&&... args
	) noexcept(
		noexcept(awaiter().await_resume(std::forward<decltype(args)>(args)...))
		)
	{
		return awaiter().await_resume(std::forward<decltype(args)>(args)...);
	}

protected:
	awaiter_type& awaiter() noexcept
	{
		return m_awaiter;
	}
};

// Stores the Awaitable object for non-reference types of Awaitable objects.
template<
	is_awaitable Awaitable
> class awaiter_wrapper_awaitable_storage
{
	Awaitable m_awaitable;

protected:
	// Construct m_awaitable from the function.
	template<
		std::invocable AwaitableFunc
	>
	awaiter_wrapper_awaitable_storage(
		AwaitableFunc& awaitableFunc
	) noexcept(noexcept(std::invoke(awaitableFunc))) :
		m_awaitable(std::invoke(awaitableFunc))
	{}

	// Get m_awaitable from the constructed value.
	template<
		std::invocable AwaitableFunc
	>
	Awaitable& get_awaitable(
		AwaitableFunc& awaitableFunc
	) noexcept
	{
		return m_awaitable;
	}
};

// Ignores the Awaitable object for reference types of Awaitable objects.
template<
	is_awaitable Awaitable
> 
requires std::is_reference_v<Awaitable>
class awaiter_wrapper_awaitable_storage<
	Awaitable
>
{
protected:
	// Do nothing.
	template<
		std::invocable AwaitableFunc
	>
	awaiter_wrapper_awaitable_storage(
		AwaitableFunc& awaitableFunc
	) noexcept
	{}

	// Get the awaitable object as from the function.
	template<
		std::invocable AwaitableFunc
	>
	decltype(auto) get_awaitable(
		AwaitableFunc& awaitableFunc
	) noexcept(noexcept(std::invoke(awaitableFunc)))
	{
		return std::invoke(awaitableFunc);
	}
};

// The primary template for awaiter_wrapper delegates to the
// is_awaiter specialization for the actual underlying awaiter,
// and obtains the awaiter from the awaitable object.
template<
	is_awaitable Awaitable
> class awaiter_wrapper
	:
	// Note that awaiter_wrapper_awaitable_storage is first so that it is
	// constructed before awaiter_wrapper and destroyed after awaiter_wrapper.
	private awaiter_wrapper_awaitable_storage<Awaitable>,
	public awaiter_wrapper<awaiter_type<Awaitable>>
{
public:
	template<
		std::invocable AwaitableFunc
	>
	requires std::is_invocable_r_v<Awaitable, AwaitableFunc>
	explicit awaiter_wrapper(
		AwaitableFunc&& awaitableFunc
	) noexcept(noexcept(get_awaiter(this->get_awaitable(awaitableFunc))))
		: 
		awaiter_wrapper_awaitable_storage<Awaitable>(awaitableFunc),
		awaiter_wrapper<awaiter_type<Awaitable>>
	{
		[&]() -> decltype(auto) { return get_awaiter(this->get_awaitable(awaitableFunc)); }
	}
	{}
};

}
using detail::awaiter_wrapper;
}