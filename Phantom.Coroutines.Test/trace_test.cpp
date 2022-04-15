#include "Phantom.Coroutines/detail/coroutine.h"
#include "async_test.h"
#include <source_location>
#include <iostream>
#include "Phantom.Coroutines/type_traits.h"

using namespace Phantom::Coroutines;

template<
	typename S
>
struct tracer
{
	S&& m_stream;

	template<
		typename S
	>
	tracer(
		S&& stream
	) : m_stream(std::forward<S>(stream))
	{}

	template<
		typename T
	> auto operator << (T&& t)
	{
		return tracer{ (m_stream << std::forward<T>(t)) };
	}

	~tracer()
	{
		m_stream << "\n";
	}
};

template<typename S>
tracer(S&& s)->tracer<S>;

[[nodiscard]] auto trace(
	std::source_location location
)
{
	return tracer{ std::cout }
		<< location.file_name()
		<< ":"
		<< location.function_name()
		<< ":"
		<< location.line()
		<< ":"
		<< location.column()
		<< ": ";
}

template<
	is_awaitable TAwaitable
>
class tracer_awaitable;

template<
	is_awaiter TAwaitable
>
class tracer_awaitable<TAwaitable>
{
	TAwaitable m_awaitable;

public:
	tracer_awaitable(
		TAwaitable&& awaitable
	) 
		: m_awaitable { std::forward<TAwaitable>(awaitable) }
	{}

	template<
		has_co_await CoAwaitable
	> tracer_awaitable(
		CoAwaitable&& awaitable
	) :
		m_awaitable(
			std::forward<CoAwaitable>(awaitable).operator co_await()
		)
	{}

	bool await_ready(
		std::source_location sourceLocation = std::source_location::current()
	)
	{
		trace(sourceLocation) << "await_ready";
		return std::forward<TAwaitable>(m_awaitable).await_ready();
	}

	auto await_suspend(
		coroutine_handle<> continuation,
		std::source_location sourceLocation = std::source_location::current()
	)
	{
		trace(sourceLocation) << "await_suspend";
		return std::forward<TAwaitable>(m_awaitable).await_suspend(continuation);
	}

	auto await_resume(
		std::source_location sourceLocation = std::source_location::current()
	)
	{
		trace(sourceLocation) << "await_resume";
		return std::forward<TAwaitable>(m_awaitable).await_resume();
	}
};

template<
	is_awaiter Awaitable
>
tracer_awaitable(Awaitable&& awaitable)->tracer_awaitable<Awaitable&&>;

template<
	has_co_await Awaitable
>
tracer_awaitable(Awaitable&& awaitable)->tracer_awaitable<awaiter_type<Awaitable>>;

ASYNC_TEST(trace_test, coroutine_tracing)
{
	co_await tracer_awaitable{ []() -> task<> { co_return; }() };
}