#include "async_test.h"
#include <variant>
#include <vector>
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/contextual_promise.h"
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/task.h"

namespace Phantom::Coroutines::Test
{
namespace 
{

enum class operation_type
{
	enter,
	leave,
	suspend,
	resume
};

struct operation
{
	operation_type m_type;
	auto operator<=>(const operation&) const = default;
};

typedef std::vector<
	operation
> operations_vector;
}

template<
	typename BasePromise
> class test_contextual_promise
	:
	public derived_promise<contextual_promise<BasePromise>>
{
public:
	template<typename Awaiter>
	struct test_contextual_promise_awaiter : public extended_awaiter<test_contextual_promise, Awaiter>
	{
		using test_contextual_promise_awaiter::extended_awaiter::extended_awaiter;

		auto await_ready()
		{
			return this->awaiter().await_ready();
		}

		auto await_suspend(
			auto&& args)
		{
			this->promise().m_operations.push_back(
				{ operation_type::suspend }
			);
			return this->awaiter().await_suspend(
				std::forward<decltype(args)>(args)...);
		}

		auto await_resume()
		{
			this->promise().m_operations.push_back(
				{ operation_type::suspend }
			);
			return this->awaiter().await_resume();
		}
	};

	template<
		typename Awaiter
	> test_contextual_promise_awaiter(test_contextual_promise&, Awaiter&&) -> test_contextual_promise_awaiter<Awaiter>;

	template<
		std::invocable AwaiterFunc
	> test_contextual_promise_awaiter(test_contextual_promise&, AwaiterFunc&&) -> test_contextual_promise_awaiter<std::invoke_result_t<AwaiterFunc>>;

	test_contextual_promise(
		auto&&,
		operations_vector& operations
	) : m_operations { operations }
	{}

	operations_vector& m_operations;

	void enter()
	{
		m_operations.push_back(
			{ operation_type::enter });
	}

	void leave()
	{
		m_operations.push_back(
			{ operation_type::leave });
	}

	auto initial_suspend(
		this auto& self)
	{
		return test_contextual_promise_awaiter
		{ 
			*this,
			[&]() { return self.test_contextual_promise::contextual_promise::initial_suspend(); }
		};
	}

	auto await_transform(
		auto&& awaitable
	)
	{
		return test_contextual_promise_awaiter
		{ 
			*this,
			contextual_promise<BasePromise>::await_transform(
				std::forward<decltype(awaitable)>(awaitable))
		};
	}

	auto final_suspend(
		this auto& self)
	{
		return test_contextual_promise_awaiter
		{
			*this,
			[&]() { return self.test_contextual_promise::contextual_promise::final_suspend(); }
		};
	}
};

template<
	typename T = void
> using test_contextual_task = basic_task<
	test_contextual_promise<task_promise<T>>>;

static_assert(is_awaiter<test_contextual_task<>::promise_type::test_contextual_promise_awaiter<async_manual_reset_event<>>>);

ASYNC_TEST(contextual_promise_test, context_enter_on_initial_suspend_leave_on_final_suspend)
{
	operations_vector operations;
	async_manual_reset_event<> event;

	auto taskLambda = [&](auto&) -> test_contextual_task<>
	{
		co_await event;
	};

	auto task = taskLambda(operations);

	EXPECT_EQ(
		operations,
		(operations_vector
		{
			{ operation_type::suspend },
		}));

	async_scope<> scope;
	scope.spawn(std::move(task));

	EXPECT_EQ(
		operations,
		(operations_vector
		{
			{ operation_type::suspend },
			{ operation_type::enter },
			{ operation_type::suspend },
			{ operation_type::leave },
		}));

	event.set();

	EXPECT_EQ(
		operations,
		(operations_vector
		{
			{ operation_type::suspend },
			{ operation_type::enter },
			{ operation_type::suspend },
			{ operation_type::leave },
			{ operation_type::resume },
			{ operation_type::enter },
			{ operation_type::suspend },
			{ operation_type::leave },
		}));
}


}
