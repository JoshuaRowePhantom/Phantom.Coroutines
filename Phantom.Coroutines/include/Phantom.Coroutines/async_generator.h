#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "await_none_await_transform.h"
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
> concept AsyncGeneratorTraits = requires
{
	typename Traits::async_generator_type;
	typename Traits::iterator_type;
	typename Traits::promise_type;
	typename Traits::increment_awaiter_type;
	typename Traits::yield_awaiter_type;
	typename Traits::result_type;
};

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator;

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator_yield_awaiter
{
public:
	using promise_type = typename Traits::promise_type;

private:
	promise_type& m_promise;

protected:
	promise_type& promise()
	{
		return m_promise;
	}

public:
	basic_async_generator_yield_awaiter(
		promise_type& promise
	) :
		m_promise(promise)
	{}

	bool await_ready() const noexcept { return false; }

	std::coroutine_handle<> await_suspend(
		std::coroutine_handle<>
	)
	{
		return promise().m_continuation;
	}

	void await_resume() const noexcept {}
};

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator_promise
	:
await_none_await_transform
{
	template<
		AsyncGeneratorTraits Traits
	> friend class basic_async_generator_iterator;

	template<
		AsyncGeneratorTraits Traits
	> friend class basic_async_generator_increment_awaiter;

	template<
		AsyncGeneratorTraits Traits
	> friend class basic_async_generator_yield_awaiter;
	
	template<
		AsyncGeneratorTraits Traits
	> friend class basic_async_generator;

	using promise_type = typename Traits::promise_type;
	using yield_awaiter_type = typename Traits::yield_awaiter_type;
	using result_type = typename Traits::result_type;
	using async_generator_type = typename Traits::async_generator_type;

	typedef std::variant<
		std::monostate,
		std::reference_wrapper<std::remove_reference_t<result_type>>,
		std::remove_cvref_t<result_type>,
		std::exception_ptr,
		std::monostate
	> current_value_holder_type;

	// The iterator needs to be advanced.
	static const std::size_t EmptyIndex = 0;
	// The iterator holds a reference to a value.
	static const std::size_t ValueRefIndex = 1;
	// The iterator holds a copy of a value.
	static const std::size_t ValueIndex = 2;
	// The iterator holds an exception.
	static const std::size_t ExceptionIndex = 3;
	// The iterator is complete.
	static const std::size_t CompleteIndex = 4;

	current_value_holder_type m_currentValue;
	coroutine_handle<> m_continuation;
public:
	async_generator_type get_return_object()
	{
		return async_generator_type{ static_cast<promise_type&>(*this) };
	}

	suspend_always initial_suspend() noexcept
	{
		return suspend_always{};
	}

	template<
		typename Value
	> yield_awaiter_type yield_value(
		Value&& value
	)
	{
		m_currentValue.emplace<ValueIndex>(
			std::forward<Value>(value));
		
		return yield_awaiter_type
		{
			static_cast<promise_type&>(*this)
		};
	}

	template<
		typename = std::enable_if_t<
			std::is_reference_v<result_type>
		>
	> yield_awaiter_type yield_value(
		result_type& value
	)
	{
		m_currentValue.emplace<ValueRefIndex>(
			static_cast<std::add_lvalue_reference_t<result_type>>(
				value));

		return yield_awaiter_type
		{
			static_cast<promise_type&>(*this)
		};
	}

	yield_awaiter_type yield_value(
		std::remove_reference_t<result_type>&& value
	)
	{
		m_currentValue.emplace<ValueRefIndex>(
			static_cast<std::add_lvalue_reference_t<result_type>>(
				value));

		return yield_awaiter_type
		{
			static_cast<promise_type&>(*this)
		};
	}

	void return_void()
	{
		m_currentValue.emplace<CompleteIndex>();
	}

	void unhandled_exception()
	{
		m_currentValue.emplace<ExceptionIndex>(
			std::current_exception());
	}

	final_suspend_transfer final_suspend() noexcept
	{
		return final_suspend_transfer
		{
			m_continuation
		};
	}
};

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator_increment_awaiter
{
	using promise_type = typename Traits::promise_type;
	using iterator_type = typename Traits::iterator_type;
	using basic_promise_type = basic_async_generator_promise<Traits>;
	promise_type* m_promise;

	promise_type* promise()
	{
		return m_promise;
	}

public:
	basic_async_generator_increment_awaiter(
		promise_type* promise
	) :
		m_promise{ promise }
	{}

	bool await_ready() const noexcept 
	{
		return !m_promise || m_promise->m_currentValue.index() != basic_promise_type::EmptyIndex;
	}

	coroutine_handle<> await_suspend(
		coroutine_handle<> continuation
	) noexcept
	{
		m_promise->m_continuation = continuation;
		return coroutine_handle<promise_type>::from_promise(*m_promise);
	}

	iterator_type await_resume()
	{
		if (m_promise && m_promise->m_currentValue.index() == basic_promise_type::ExceptionIndex)
		{
			std::rethrow_exception(
				std::get<basic_promise_type::ExceptionIndex>(
					m_promise->m_currentValue));
		}

		return iterator_type{ m_promise };
	}
};

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator_iterator
{
	using promise_type = typename Traits::promise_type;
	using async_generator_type = typename Traits::async_generator_type;
	using result_type = typename Traits::result_type;
	using basic_promise_type = basic_async_generator_promise<Traits>;
	using increment_awaiter_type = typename Traits::increment_awaiter_type;

	promise_type* m_promise;

public:
	typedef std::remove_reference_t<result_type> value_type;
	typedef size_t difference_type;
	typedef std::add_lvalue_reference_t<result_type> reference;
	typedef std::input_iterator_tag iterator_category;

	basic_async_generator_iterator()
		:
		m_promise{ nullptr }
	{}

	basic_async_generator_iterator(
		promise_type* promise
	) :
		m_promise { promise }
	{
		if (m_promise && m_promise->m_currentValue.index() == basic_promise_type::CompleteIndex)
		{
			m_promise = nullptr;
		}
	}

	increment_awaiter_type operator++()
	{
		m_promise->m_currentValue.emplace<basic_promise_type::EmptyIndex>();
		return increment_awaiter_type
		{
			m_promise
		};
	}

	std::add_lvalue_reference_t<result_type> operator*()
	{
		if (m_promise->m_currentValue.index() == basic_promise_type::ValueIndex)
		{
			return std::get<basic_promise_type::ValueIndex>(
				m_promise->m_currentValue);
		}

		return std::get<basic_promise_type::ValueRefIndex>(
			m_promise->m_currentValue);
	}

	std::remove_reference_t<result_type>* operator->()
	{
		return &*this;
	}

	explicit operator bool() const
	{
		return m_promise 
			&& m_promise->m_currentValue.index() != basic_promise_type::CompleteIndex;
	}

	bool operator==(
		const basic_async_generator_iterator& other
		)
		const
	{
		return m_promise == other.m_promise
			|| !*this && !other;
	}

	bool operator!=(
		const basic_async_generator_iterator& other
		)
		const
	{
		return !(m_promise == other.m_promise)
			|| (!*this != !other);
	}
};

template<
	AsyncGeneratorTraits Traits
> class basic_async_generator
{
	template<
		AsyncGeneratorTraits Traits
	> friend class basic_async_generator_iterator;
	
	using basic_promise_type = basic_async_generator_promise<Traits>;

public:
	using promise_type = typename Traits::promise_type;
	using async_generator_type = typename Traits::async_generator_type;
	using iterator_type = typename Traits::iterator_type;
	using increment_awaiter_type = typename Traits::increment_awaiter_type;

private:
	promise_type* m_promise;

public:
	basic_async_generator()
		: 
		m_promise { nullptr }
	{}

	basic_async_generator(
		promise_type& promise
	) :
		m_promise
	{
		&promise
	}
	{}

	basic_async_generator(
		const basic_async_generator&
	) = delete;

	basic_async_generator(
		basic_async_generator&& other
	) :
		m_promise{ other.m_promise }
	{
		other.m_promise = nullptr;
	}

	void operator=(
		const basic_async_generator&
		) = delete;

	basic_async_generator& operator=(
		basic_async_generator&& other
		)
	{
		std::swap(m_promise, other.m_promise);
		return *this;
	}

	~basic_async_generator() 
	{
		if (m_promise)
		{
			coroutine_handle<promise_type>::from_promise(*m_promise).destroy();
		}
	}

	increment_awaiter_type begin()
	{
		return increment_awaiter_type{ m_promise };
	}

	iterator_type end() const
	{ 
		return iterator_type{};
	}
};

template<
	typename TResult
> class async_generator;

template<
	typename TResult
> class async_generator_promise;

template<
	typename TResult
> class async_generator_iterator;

template<
	typename TResult
> class async_generator_increment_awaiter;

template<
	typename TResult
> class async_generator_yield_awaiter;

template<
	typename TResult
> struct async_generator_traits
{
	typedef async_generator<TResult> async_generator_type;
	typedef async_generator_promise<TResult> promise_type;
	typedef async_generator_iterator<TResult> iterator_type;
	typedef TResult result_type;
	typedef async_generator_increment_awaiter<TResult> increment_awaiter_type;
	typedef async_generator_yield_awaiter<TResult> yield_awaiter_type;
};

template<
	typename TResult
> class async_generator
	:
public basic_async_generator<
	async_generator_traits<TResult>
>
{};

template<
	typename TResult
> class async_generator_promise
	:
public basic_async_generator_promise<
	async_generator_traits<TResult>
>
{};

template<
	typename TResult
> class async_generator_iterator
	:
public basic_async_generator_iterator<
	async_generator_traits<TResult>
>
{
public:
	using async_generator_iterator::basic_async_generator_iterator::basic_async_generator_iterator;
};

template<
	typename TResult
> class async_generator_increment_awaiter
	:
public basic_async_generator_increment_awaiter<
	async_generator_traits<TResult>
>
{
};

template<
	typename TResult
> class async_generator_yield_awaiter
	:
public basic_async_generator_yield_awaiter<
	async_generator_traits<TResult>
>
{};

}

using detail::basic_async_generator;
using detail::basic_async_generator_iterator;
using detail::basic_async_generator_promise;
using detail::basic_async_generator_increment_awaiter;
using detail::basic_async_generator_yield_awaiter;
using detail::async_generator;
using detail::AsyncGeneratorTraits;

}
