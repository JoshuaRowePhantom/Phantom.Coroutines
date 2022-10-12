#pragma once

#if PHANTOM_COROUTINES_ICE_DEDUCE_THIS_PROMISE
namespace Phantom::Coroutines::detail
{

// On awaiters, MSVC produces ICE when deducing "this" on
// await_ready
// await_resume
template<
	typename Awaiter
> class deduce_this_awaiter_workaround
{
	Awaiter awaiter;

	decltype(auto) await_ready() noexcept(noexcept(Awaiter::await_ready()))
	{
		return Awaiter::await_ready(*this);
	}

	decltype(auto) await_resume() noexcept(noexcept(Awaiter::await_resume()))
	{
		return Awaiter::await_resume(*this);
	}
};

// On a "promise" object, MSVC produces ICE when deducing "this" on
// initial_suspend
// final_suspend
// get_return_object
// unhandled_exception
template<
	typename Promise
> class deduce_this_promise_workaround
	:
public Promise
{
	using Promise::Promise;

	decltype(auto) initial_suspend() noexcept(noexcept(Promise::initial_suspend()))
	{
		return Promise::initial_suspend(*this);
	}

	decltype(auto) final_suspend() noexcept(noexcept(Promise::final_suspend()))
	{
		return Promise::final_suspend(*this);
	}

	decltype(auto) get_return_object() noexcept(noexcept(Promise::get_return_object()))
	{
		return Promise::get_return_object(*this);
	}

	decltype(auto) unhandled_exception() noexcept(noexcept(Promise::unhandled_exception()))
	{
		return Promise::unhandled_exception(*this);
	}
};

}
#endif
