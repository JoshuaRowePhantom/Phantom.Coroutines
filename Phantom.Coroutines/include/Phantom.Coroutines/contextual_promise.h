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
	noexcept(promise.leave());
};

template<
	is_extensible_promise BasePromise
> class contextual_promise
	:
public derived_promise<BasePromise>
{
	struct DoNotEnterOnResume {};
	struct DoNotLeaveOnSuspend {};
	struct DoEnterOnResume {};
	struct DoLeaveOnSuspend {};

	template<
		typename Enter,
		typename Leave,
		typename Promise,
		is_awaitable Awaiter
	> class contextual_promise_awaiter :
		public extended_awaiter<Promise, Awaiter>
	{
		bool m_bSuspended = false;

		using contextual_promise_awaiter::extended_awaiter::awaiter;
		using contextual_promise_awaiter::extended_awaiter::handle;

	public:
		contextual_promise_awaiter(
			Enter enter,
			Leave leave,
			Promise& promise,
			std::invocable auto&& awaitableFunc
		) : contextual_promise_awaiter::extended_awaiter::extended_awaiter
		{
			promise,
			std::forward<decltype(awaitableFunc)>(awaitableFunc)
		}
		{}

		bool await_ready(
			auto&&... args
		) noexcept(
			noexcept(awaiter().await_ready(std::forward<decltype(args)>(args)...))
			)
		{
			return awaiter().await_ready(std::forward<decltype(args)>(args)...);
		}

		auto await_suspend(
			auto&&... args
		) noexcept(
			noexcept(awaiter().await_suspend(std::forward<decltype(args)>(args)...))
			)
		{
			m_bSuspended = true;
			if (std::same_as<DoLeaveOnSuspend, Leave>)
			{
				this->promise().leave();
			}
			return awaiter().await_suspend(std::forward<decltype(args)>(args)...);
		}

		auto await_resume(
			auto&&... args
		) noexcept /* noexcept(
			noexcept(
				awaiter().await_resume(std::forward<decltype(args)>(args)...))
				&& (std::same_as<DoNotEnterOnResume, Enter> || noexcept(this->promise().enter())
		)) */
		{
			if (std::same_as<DoEnterOnResume, Enter> && m_bSuspended)
			{
				this->promise().enter();
			}
			return awaiter().await_resume(std::forward<decltype(args)>(args)...);
		}
	};

	template<
		typename Enter,
		typename Leave,
		typename Promise,
		is_awaitable Awaitable
	> contextual_promise_awaiter(Enter, Leave, Promise&, Awaitable&&) -> contextual_promise_awaiter<Enter, Leave, Promise, Awaitable>;

	template<
		typename Enter,
		typename Leave,
		typename Promise,
		std::invocable AwaitableFunc
	> contextual_promise_awaiter(Enter, Leave, Promise&, AwaitableFunc&&) -> contextual_promise_awaiter<Enter, Leave, Promise, std::invoke_result_t<AwaitableFunc>>;

public:
	using contextual_promise::derived_promise::derived_promise;

	auto initial_suspend(
		this auto& self
	) noexcept(noexcept(
		self.derived_promise<BasePromise>::initial_suspend()
		))
	{
		static_assert(is_contextual_promise<decltype(self)>);

		return contextual_promise_awaiter
		{
			DoEnterOnResume{},
			DoNotLeaveOnSuspend{},
			self,
			[&]() -> decltype(auto)
			{
				return self.derived_promise<BasePromise>::initial_suspend();
			}
		};
	}

	auto final_suspend(
		this auto& self
	) noexcept
	{
		static_assert(is_contextual_promise<decltype(self)>);

		return contextual_promise_awaiter
		{
			DoNotEnterOnResume{},
			DoLeaveOnSuspend{},
			self,
			[&]() noexcept -> decltype(auto)
			{
				return self.derived_promise<BasePromise>::final_suspend();
			}
		};
	}

	auto await_transform(
		this auto& self,
		auto&& awaitable)
	{
		static_assert(is_contextual_promise<decltype(self)>);

		return contextual_promise_awaiter
		{
			DoEnterOnResume{},
			DoLeaveOnSuspend{},
			self,
			[&]() noexcept(noexcept(
				self.derived_promise<BasePromise>::await_transform(
					std::forward<decltype(awaitable)>(awaitable))
				)) -> decltype(auto)
			{
				return self.derived_promise<BasePromise>::await_transform(
					std::forward<decltype(awaitable)>(awaitable));
			}
		};
	}
};

}

using detail::is_contextual_promise;
using detail::contextual_promise;

}