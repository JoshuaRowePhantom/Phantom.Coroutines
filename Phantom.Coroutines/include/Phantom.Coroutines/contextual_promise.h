#include "extensible_promise.h"
#include "thread_local_context.h"

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
	is_contextual_promise ContextualPromise,
	typename ExtendedPromise = ContextualPromise
> class contextual_promise
	:
public derived_promise<BasePromise>,
public extensible_promise<ExtendedPromise>
{
	class key {};

	const bool DoNotEnterOnResume = false;
	const bool DoNotLeaveOnSuspend = false;
	const bool DoEnterOnResume = true;
	const bool DoLeaveOnSuspend = true;

	template<
		bool Enter,
		bool Leave,
		is_awaiter Awaiter
	> class awaiter :
		public awaiter_wrapper<Awaiter>
	{
		bool m_bSuspended = false;
		ExtendedPromise& m_promise;

		using awaiter_wrapper<Awaiter>::get_awaiter;

	public:
		template<
			typename AwaiterArg
		> awaiter(
			ExtendedPromise& promise,
			AwaiterArg&& awaiter,
			key
		) : 
			awaiter_wrapper<Awaiter>{ awaiter },
			m_promise{ promise }
		{}

		auto await_suspend(
			auto&&... args
		) noexcept(
			noexcept(get_awaiter().await_suspend(std::forward<decltype(args)>(args)...))
			&& noexcept(m_promise.leave())
			)
		{
			m_bSuspended = true;
			if (Leave)
			{
				m_promise.leave();
			}
			return get_awaiter().await_suspend(std::forward<decltype(args)>(args)...);
		}

		auto await_resume(
			auto&&... args
		) noexcept(
			noexcept(get_awaiter().await_resume(std::forward<decltype(args)>(args)...))
			&& noexcept(m_promise.enter())
			)
		{
			if (Enter && m_bSuspended)
			{
				m_promise.enter();
			}
			return get_awaiter().await_resume(std::forward<decltype(args)>(args)...);
		}
	};

	template<
		bool Enter,
		bool Leave,
		is_awaiter Awaiter
	> awaiter(Awaiter&&)->awaiter<Enter, Leave, Awaiter>;

public:
	using extensible_promise<ExtendedPromise>::extensible_promise;

	auto initial_suspend()
	{
		return awaiter<DoEnterOnResume, DoNotLeaveOnSuspend>
		{
			*this,
			wrapper_promise<BasePromise>::initial_suspend(),
			key()
		};
	}

	auto final_suspend()
	{
		return awaiter<DoNotEnterOnResume, DoLeaveOnSuspend>
		{
			*this,
				wrapper_promise<BasePromise>::initial_suspend(),
				key()
		};
	}

	auto await_transform(
		auto&&... args)
	{
		return awaiter<DoEnterOnResume, DoLeaveOnSuspend>
		{
			*this,
			wrapper_promise<BasePromise>::await_transform(
				std::forward<decltype(args)>(args)...),
			key()
		};
	}
};

template<
	typename BasePromise,
	is_thread_local_context ThreadLocalContext,
	typename ExtendedPromise = thread_local_contextual_promise<BasePromise, ThreadLocalContext>
> class thread_local_contextual_promise
	:
public derived_promise<
	contextual_promise<
		BasePromise,
		thread_local_contextual_promise,
		ExtendedPromise
	>>
{
	using base_promise = thread_local_contextual_promise::derived_promise;
	using thread_local_context_scope = thread_local_context_scope<ThreadLocalContext>;

public:
	using value_type = typename ThreadLocalContext::value_type;

private:
	std::optional<thread_local_context_scope> m_scope;
	std::optional<value_type> m_value;

public:
	template<
		typename... Args
	> thread_local_contextual_promise(
		Args&&... args
	) :
		m_value
	{
		ThreadLocalContext::current()
	}
	{}

	using base_promise::base_promise;

	void enter()
	{
		m_scope.emplace(thread_local_context_scope{ std::move(*m_value) });
		m_value.reset();
	}

	void leave()
	{
		m_value.emplace(std::move(ThreadLocalContext::current()));
		m_scope.reset();
	}
};

}
}