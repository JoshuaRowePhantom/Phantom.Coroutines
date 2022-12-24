#include "detail/immovable_object.h"
#include "detail/storage_for.h"
#include "Phantom.Coroutines/type_traits.h"
#include "async_manual_reset_event.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename Value,
	is_template_instantiation<basic_async_manual_reset_event> Event
> class basic_async_promise;

template<
	typename Value,
	is_async_manual_reset_event_policy... Policy
> using async_promise = basic_async_promise<
	Value,
	async_manual_reset_event<Policy...>
>;

template<
	typename Value,
	is_template_instantiation<basic_async_manual_reset_event> Event
> class basic_async_promise
	:
	storage_for<Value>,
	immovable_object
{
	Event m_event;

	typedef awaiter_type<async_manual_reset_event<>> manual_reset_event_awaiter_type;

	struct awaiter_key {};

	class awaiter
	{
		basic_async_promise& m_promise;
		manual_reset_event_awaiter_type m_manualResetEventAwaiter;

	public:
		awaiter(
			basic_async_promise& promise,
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

		Value& await_resume() const noexcept
		{
			return m_promise->as<Value>();
		}
	};

public:
	basic_async_promise()
	{}

	template<
		typename... Args
	> basic_async_promise(
		Args&&... args
	)
	{
		emplace(
			std::forward<Args>(args)...
		);
	}

	~basic_async_promise()
	{
		if (m_event.is_set())
		{
			this->destroy<Value>();
		}
	}

	awaiter operator co_await() const noexcept
	{
		return awaiter{ *this };
	}

	template<
		typename ... Args
	> Value& emplace(
		Args&&... args
	)
	{
		assert(!m_event.is_set());

		auto& result = basic_async_promise::storage_for::emplace(
			std::forward<Args>(args)...
		);

		m_event.set();

		return result;
	}
};
}

using detail::async_promise;

}