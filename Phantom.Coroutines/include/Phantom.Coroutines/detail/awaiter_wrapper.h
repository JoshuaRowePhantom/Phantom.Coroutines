#pragma once
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_awaitable Awaitable
> class awaiter_wrapper;

template<
	is_awaiter Awaiter
> class awaiter_wrapper<
	Awaiter
>
{
protected:
	typedef Awaiter awaiter_type;

private:
	awaiter_type m_awaiter;

public:
	template<
		typename AwaiterArg
	>
	awaiter_wrapper(
		AwaiterArg&& awaiter
	) : m_awaiter(std::forward<AwaiterArg>(awaiter))
	{}

	auto await_ready(
		auto&&... args
	) noexcept(noexcept(awaiter().await_ready(std::forward<decltype(args)>(args)...)))
	{
		return awaiter().await_ready(
			std::forward<decltype(args)>(args)...
		);
	}

	auto await_suspend(
		auto&&... args
	) noexcept(
		noexcept(awaiter().await_suspend(std::forward<decltype(args)>(args)...))
		)
	{
		return awaiter().await_suspend(std::forward<decltype(args)>(args)...);
	}

	auto await_resume(
		auto&&... args
	) noexcept(
		noexcept(awaiter().await_resume(std::forward<decltype(args)>(args)...))
		)
	{
		return awaiter().await_resume(std::forward<decltype(args)>(args)...);
	}

protected:
	awaiter_type& awaiter()
	{
		return m_awaiter;
	}
};

template<
	is_awaitable Awaitable
> class awaiter_wrapper
{
protected:
	typedef decltype(detail::get_awaiter(std::declval<Awaitable>())) awaiter_type;
	awaiter_type m_awaiter;

public:
	template<
		typename AwaitableArg
	>
	awaiter_wrapper(
		AwaitableArg&& awaitable
	) : m_awaiter
	{
		detail::get_awaiter(
			std::forward<AwaitableArg>(awaitable))
	}
	{}

protected:
	awaiter_type& awaiter()
	{
		return m_awaiter;
	}
};

}
using detail::awaiter_wrapper;
}