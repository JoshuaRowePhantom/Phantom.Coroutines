#pragma once

#include "early_termination_task.h"
#include <system_error>

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_early_termination_promise Promise
>
class error_condition_early_termination_await_transformer
{
	class awaiter : basic_early_termination_transformed_awaiter<Promise>
	{
		template<
			is_early_termination_promise Promise
		>
		friend class error_condition_early_termination;

		std::error_condition m_errorCondition;

		awaiter(
			error_condition_early_termination_await_transformer& transformer,
			std::error_condition errorCondition
		) :
			basic_early_termination_awaiter<Promise>{ transformer }
		{}

	public:
		bool await_ready() const noexcept
		{
			return !m_errorCondition;
		}

		auto await_suspend() noexcept
		{
			this->return_value(
				early_termination_result{ m_errorCondition }
			);
			return this->resume();
		}

		void await_resume() const noexcept
		{
			// This method will only be called if m_errorCondition
			// did not contain an error condition.
		}
	};

public:
	awaiter await_transform(
		std::error_condition errorCondition
	)
	{
		return awaiter
		{
			*this,
			errorCondition
		};
	}
};

}
}
