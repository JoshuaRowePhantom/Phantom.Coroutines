import Phantom.Coroutines.early_termination_task;
import <system_error>;

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_basic_early_termination_promise Promise
>
class error_condition_early_termination_await_transformer
{
	class awaiter : basic_early_termination_awaiter<Promise>
	{
		template<
			is_basic_early_termination_promise Promise
		>
		friend class error_condition_early_termination;

		std::error_condition m_errorCondition;

	public:
		awaiter(
			error_condition_early_termination_await_transformer& transformer,
			std::error_condition errorCondition
		) :
			basic_early_termination_awaiter<Promise>{ transformer }
		{}

		bool await_ready() const noexcept
		{
			return !m_errorCondition;
		}

		auto await_suspend() noexcept
		{
			this->set_result(
				early_termination_result{ m_errorCondition }
			);
			return this->resume();
		}

		void await_resume() const noexcept
		{}
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
