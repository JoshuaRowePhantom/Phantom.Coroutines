#pragma once

#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#include <concepts>
#include <exception>
#include <variant>
#include <type_traits>


namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename Traits
> concept GeneratorTraits = requires
{
	typename Traits::generator_type;
	typename Traits::iterator_type;
	typename Traits::promise_type;
	typename Traits::result_type;
};

template<
	GeneratorTraits Traits
> class basic_generator;

template<
	GeneratorTraits Traits
> class basic_generator_promise
{
	using typename Traits::promise_type;
	using typename Traits::result_type;
	using typename Traits::generator_type;

	typedef std::variant<
		std::monostate,
		result_type&,
		std::exception_ptr
	> current_value_holder_type;

	size_t EmptyIndex = 0;
	size_t ValueIndex = 1;
	size_t ExceptionIndex = 2;

	current_value_holder_type m_currentValue;

public:
	generator_type get_return_object()
	{
		return generator_type{ static_cast<promise_type>(*this) };
	}

	suspend_never initial_suspend() noexcept
	{
		return suspend_never{};
	}

	template<
		typename Value
	> suspend_always yield_value(
		Value&& value
	)
	{
		m_currentValue.emplace<ValueIndex>(
			std::forward<Value>(
				value
				));
		return suspend_always{};
	}

	template<
		typename T
	> void await_transform(
		T&&
	) = delete;

	void return_void()
	{
		m_currentValue.emplace<EmptyIndex>();
	}

	void unhandled_exception()
	{
		m_currentValue.emplace<ExceptionIndex>(
			std::current_exception());
	}

	suspend_always final_suspend() noexcept
	{
		return suspend_always{};
	}
};

template<
	GeneratorTraits Traits
> class basic_generator_iterator
{
	using typename Traits::promise_type;
	using typename Traits::result_type;
	using basic_promise_type = basic_generator_promise<Traits>;

	promise_type* m_promise;

public:
	basic_generator_iterator& operator++()
	{
		std::coroutine_handle<promise_type>::from_promise(*m_promise).resume();

		if (m_promise->m_currentValue.index() == basic_promise_type::ExceptionIndex)
		{
			std::rethrow_exception(
				std::get<basic_promise_type::ExceptionIndex>(
					m_promise->m_currentValue));
		}
	}

	result_type& operator*()
	{
		return std::get<basic_promise_type::ValueIndex>(
			m_promise.m_currentValue);
	}

	bool operator==(
		const basic_generator_iterator& other
		)
		const
	{
		return m_promise == other.m_promise;
	}

	bool operator!=(
		const basic_generator_iterator& other
		)
		const
	{
		return m_promise != other.m_promise;
	}
};

template<
	GeneratorTraits Traits
> class basic_generator
{
public:
	using typename Traits::promise_type;
	using typename Traits::generator_type;
	using typename Traits::iterator_type;

private:
	promise_type* m_promise;

public:
	basic_generator()
		: 
		m_promise { nullptr }
	{}

	basic_generator(
		promise_type& promise
	) :
		m_promise
	{
		&promise
	}
	{}

	basic_generator(
		const basic_generator&
	) = delete;

	basic_generator(
		basic_generator&& other
	) :
		m_promise{ other.m_promise }
	{
		other.m_promise = nullptr;
	}

	void operator=(
		const basic_generator&
		) = delete;

	basic_generator& operator=(
		basic_generator&& other
		)
	{
		std::swap(m_promise, other.m_promise);
		return *this;
	}

	~basic_generator() 
	{
		if (m_promise)
		{
			coroutine_handle<promise_type>::from_promise(*m_promise).destroy();
		}
	}

	iterator_type begin()
	{
		return iterator_type{ static_cast<generator_type>(*this) };
	}

	iterator_type end() const 
	{ 
		return iterator_type{};
	}
};

template<
	typename TResult
> class generator;

template<
	typename TResult
> class generator_promise;

template<
	typename TResult
> class generator_iterator;

template<
	typename TResult
> struct generator_traits
{
	typedef generator<TResult> generator_type;
	typedef generator_promise<TResult> promise_type;
	typedef generator_iterator<TResult> iterator_type;
	typedef TResult result_type;
};

template<
	typename TResult
> class generator
	:
public basic_generator<
	generator_traits<TResult>
>
{};

template<
	typename TResult
> class generator_promise
	:
public basic_generator_promise<
	generator_traits<TResult>
>
{};

template<
	typename TResult
> class generator_iterator
	:
public basic_generator_iterator<
	generator_traits<TResult>
>
{};

}
}
