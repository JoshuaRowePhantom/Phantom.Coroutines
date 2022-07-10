export module Phantom.Coroutines.async_promise;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.storage_for;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.async_manual_reset_event;

import <assert.h>;

namespace Phantom::Coroutines
{
export template<
	typename T
> class async_promise
	:
	private storage_for<T>,
	immovable_object
{
	async_manual_reset_event m_event;

	typedef awaiter_type<async_manual_reset_event> manual_reset_event_awaiter_type;

	struct awaiter_key {};

	class awaiter
	{
		async_promise& m_promise;
		manual_reset_event_awaiter_type m_manualResetEventAwaiter;

	public:
		awaiter(
			async_promise& promise,
			awaiter_key = {}
		) :
			m_promise(promise),
			m_manualResetEventAwaiter(get_awaiter(promise.m_event))
		{}

		bool await_ready() const noexcept
		{
			return m_manualResetEventAwaiter.await_ready();
		}

		auto await_suspend(auto coroutine) const noexcept
		{
			return m_manualResetEventAwaiter.await_suspend(coroutine);
		}

		T& await_resume() const noexcept
		{
			return m_promise->as<T>();
		}
	};

public:
	async_promise()
	{}

	template<
		typename... Args
	> async_promise(
		Args&&... args
	)
	{
		emplace(
			std::forward<Args>(args)...
		);
	}

	~async_promise()
	{
		if (m_event.is_set())
		{
			this->template destroy<T>();
		}
	}

	awaiter operator co_await() const noexcept
	{
		return awaiter{ *this };
	}

	template<
		typename ... Args
	> T& emplace(
		Args&&... args
	)
	{
		assert(!m_event.is_set());

		auto& result = async_promise::storage_for::emplace(
			std::forward<Args>(args)...
		);

		m_event.set();

		return result;
	}
};
}