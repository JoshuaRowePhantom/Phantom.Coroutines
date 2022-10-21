#include "extensible_promise.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename Promise
> concept is_contextual_promise = requires (Promise promise)
{
	{ promise.enter() };
	{ promise.leave() };
};

template<
	typename BasePromise,
	is_contextual_promise ContextualPromise
> class contextual_promise
	:
public derived_promise<BasePromise>,
public extensible_promise
{
	const bool DoNotEnterOnResume = false;
	const bool DoNotLeaveOnSuspend = false;
	const bool DoEnterOnResume = true;
	const bool DoLeaveOnSuspend = true;

	template<
		bool Enter,
		bool Leave,
		typename Promise,
		is_awaitable Awaiter
	> class awaiter :
		public extended_awaiter<Awaiter, Promise>
	{
		bool m_bSuspended = false;

		using awaiter_wrapper<Awaiter>::awaiter;
		using awaiter_wrapper<Awaiter>::handle;

	public:
		using awaiter::extended_awaiter::extended_awaiter;

		auto await_suspend(
			auto&&... args
		) noexcept(
			noexcept(awaiter().await_suspend(std::forward<decltype(args)>(args)...))
			&& (!Leave || noexcept(this->promise().leave()))
			)
		{
			m_bSuspended = true;
			if (Leave)
			{
				this->promise().leave();
			}
			return awaiter().await_suspend(std::forward<decltype(args)>(args)...);
		}

		auto await_resume(
			auto&&... args
		) noexcept(
			noexcept(awaiter().await_resume(std::forward<decltype(args)>(args)...))
			&& (!Enter || noexcept(this->promise().enter()))
			)
		{
			if (Enter && m_bSuspended)
			{
				this->promise().enter();
			}
			return awaiter().await_resume(std::forward<decltype(args)>(args)...);
		}
	};

	template<
		bool Enter,
		bool Leave,
		typename Promise,
		is_awaiter Awaiter
	> awaiter(Promise&, Awaiter&&)->awaiter<Enter, Leave, Promise, Awaiter>;

public:
	using contextual_promise::derived_promise::derived_promise;

	auto initial_suspend(
		this auto& self)
	{
		return awaiter<DoEnterOnResume, DoNotLeaveOnSuspend>
		{
			self,
			wrapper_promise<BasePromise>::initial_suspend(),
		};
	}

	auto final_suspend(
		this auto& self)
	{
		return awaiter<DoNotEnterOnResume, DoLeaveOnSuspend>
		{
			self,
			wrapper_promise<BasePromise>::final_suspend(),
		};
	}

	auto await_transform(
		this auto& self,
		auto&&... args)
	{
		return awaiter<DoEnterOnResume, DoLeaveOnSuspend>
		{
			self,
			wrapper_promise<BasePromise>::await_transform(
				std::forward<decltype(args)>(args)...),
		};
	}
};

}
}