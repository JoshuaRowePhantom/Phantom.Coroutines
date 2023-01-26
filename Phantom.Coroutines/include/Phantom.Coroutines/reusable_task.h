#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "detail/variant_result_storage.h"
#include <concepts>
#include <exception>
#include <type_traits>
#include <variant>
#include "extensible_promise.h"
#include "policies.h"

namespace Phantom::Coroutines::detail
{

template<
    typename Result,
    is_continuation Continuation
> class basic_reusable_task_promise;

template<
    typename Policy
> concept is_reusable_task_policy =
is_continuation_type_policy<Policy>;

template<
    typename Result,
    is_reusable_task_policy ... Policies
> 
using reusable_task_promise = basic_reusable_task_promise<
    Result,
    select_continuation_type<
        Policies..., 
        continuation_type<coroutine_handle<>>>
>;

template<
    typename Promise
> class basic_reusable_task;

template<
    typename Result = void,
    is_reusable_task_policy... Policies
> using reusable_task = basic_reusable_task<reusable_task_promise<Result, Policies...>>;

template<
    typename Promise
> class reusable_task_awaiter_base;

template<
    typename Result
>
class basic_reusable_task_variant_result
    :
    public variant_result_storage<Result>
{
public:
    typedef std::variant<
        std::monostate,
        typename variant_result_storage<Result>::result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    static const size_t result_index = 1;
    static const size_t exception_index = 2;
};

template<
    typename Result,
    is_continuation Continuation
> class basic_reusable_task_promise
    :
    public extensible_promise,
    public variant_return_result<Result>,
    private basic_reusable_task_variant_result<Result>
{
    using variant_result_storage<Result>::is_void;

    template<
        typename Promise
    > friend class basic_reusable_task;

    template<
        typename Promise
    > friend class reusable_task_awaiter_base;

private:

    using typename basic_reusable_task_promise::basic_reusable_task_variant_result::result_variant_type;
    using basic_reusable_task_promise::basic_reusable_task_variant_result::result_index;
    using basic_reusable_task_promise::basic_reusable_task_variant_result::exception_index;
    result_variant_type m_result;

    Continuation m_continuation;

protected:
    Continuation& continuation()
    {
        return m_continuation;
    }

public:
    typedef Result result_type;
    typedef Continuation continuation_type;

    auto initial_suspend(
    ) noexcept
    {
        return suspend_always{};
    }

    auto final_suspend(
    ) noexcept
    {
        return final_suspend_transfer{ continuation() };
    }

    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return basic_reusable_task(
            self.handle()
            );
    }

    decltype(auto) return_exception(
        std::exception_ptr exception)
    {
        m_result.emplace<exception_index>(
            std::move(exception));
    }

    void return_variant_result(
        auto&& value
    )
    {
        m_result.emplace<result_index>(
            std::forward<decltype(value)>(value));
    }

    void unhandled_exception(
        this auto& self
    )
    {
        return self.return_exception(
            std::current_exception());
    }
};

template<
    typename Promise
> class reusable_task_awaiter_base 
    :
public extensible_promise_handle<Promise>,
private basic_reusable_task_variant_result<typename Promise::result_type>
{
protected:
    using reusable_task_awaiter_base::basic_reusable_task_variant_result::result_index;
    using reusable_task_awaiter_base::basic_reusable_task_variant_result::exception_index;

    template<
        typename Result,
        is_continuation Continuation
    > friend class basic_reusable_task_promise;

    using typename reusable_task_awaiter_base::basic_reusable_task_variant_result::result_variant_type;

    auto& result() const
    {
        return this->promise().m_result;
    }

    bool has_exception(
    ) const noexcept
    {
        return result().index() == exception_index;
    }

    [[noreturn]] 
    void resume_exception(
    )
    {
        std::rethrow_exception(
            std::move(
                get<exception_index>(
                    result()))
        );
    }

public:
    using reusable_task_awaiter_base::extensible_promise_handle::extensible_promise_handle;

    bool await_ready(
    ) const noexcept
    {
        return this->handle() && this->handle().done();
    }

    auto await_suspend(
        auto awaiter
    ) noexcept
    {
        this->promise().continuation() = awaiter;
        return this->handle();
    }

    decltype(auto) get_result_value(
        std::invocable auto&& expression
    )
    {
        return std::forward<decltype(expression)>(expression)();
    }

    decltype(auto) await_resume_value(
        std::invocable auto&& valueFunction)
    {
        if (this->has_exception())
        {
            this->resume_exception();
        }

        return std::invoke(
            std::forward<decltype(valueFunction)>(valueFunction));
    }
};

template<
    typename Promise
> 
class [[nodiscard]] basic_reusable_task
    :
    public single_owner_promise_handle<Promise>,
    private basic_reusable_task_variant_result<typename Promise::result_type>
{
    using basic_reusable_task::basic_reusable_task_variant_result::result_index;
    using basic_reusable_task::basic_reusable_task_variant_result::exception_index;
public:
    using single_owner_promise_handle<Promise>::single_owner_promise_handle;
    using promise_type = Promise;

    auto operator co_await(
        this auto&& self
        )
    {
        struct awaiter : reusable_task_awaiter_base<Promise>
        {
            using awaiter::reusable_task_awaiter_base::reusable_task_awaiter_base;

            decltype(auto) await_resume()
            {
                return this->await_resume_value(
                    [&]() -> decltype(auto)
                {
                    if constexpr (std::is_rvalue_reference_v<decltype(self)>)
                    {
                        return this->promise().resume_variant_result<result_index>(
                            this->promise().m_result);
                    }
                    else
                    {
                        return this->promise().get_result<result_index>(
                            this->promise().m_result);
                    }
                });
            }
        };

        return awaiter
        {
            self.promise(),
        };
    }
};

template<
    typename Promise
> basic_reusable_task(coroutine_handle<Promise>) -> basic_reusable_task<Promise>;

}

namespace Phantom::Coroutines
{
using detail::basic_reusable_task;
using detail::basic_reusable_task_promise;
using detail::reusable_task;
using detail::reusable_task_promise;

}
