#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "detail/scope_guard.h"
#include "detail/variant_result_storage.h"
#include "single_consumer_promise.h"
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
> class basic_task_promise;

template<
    typename Policy
> concept is_task_policy =
is_continuation_type_policy<Policy>;

template<
    typename Result,
    is_task_policy ... Policies
> 
using task_promise = basic_task_promise<
    Result,
    select_continuation_type<
        Policies..., 
        continuation_type<coroutine_handle<>>>
>;

template<
    typename Promise
> class basic_task;

template<
    typename Result = void,
    is_task_policy... Policies
> using task = basic_task<task_promise<Result, Policies...>>;

template<
    typename Promise
> class task_awaiter;

template<
    typename Result
>
class basic_task_variant_result
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
> class basic_task_promise
    :
    public extensible_promise,
    public variant_return_result<Result>,
    private basic_task_variant_result<Result>
{
    using variant_result_storage<Result>::is_void;

    template<
        typename Promise
    > friend class basic_task;

    template<
        typename Promise
    > friend class task_awaiter;

private:

    using typename basic_task_promise::basic_task_variant_result::result_variant_type;
    using basic_task_promise::basic_task_variant_result::result_index;
    using basic_task_promise::basic_task_variant_result::exception_index;
    result_variant_type* m_result;

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
        this auto& self
    ) noexcept
    {
        return suspend_always{};
    }

    auto final_suspend(
        this auto& self
    ) noexcept
    {
        return final_suspend_transfer{ self.continuation() };
    }

    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return basic_task(
            self.handle()
            );
    }

    decltype(auto) return_exception(
        this auto& self,
        std::exception_ptr exception)
    {
        self.m_result->emplace<exception_index>(
            std::move(exception));
    }

    void return_variant_result(
        this auto& self,
        auto&& value
    )
    {
        self.m_result->emplace<result_index>(
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
> using task_awaitable = single_owner_promise_handle
<
    Promise
>;

template<
    typename Promise
> class task_awaiter 
    :
public task_awaitable<Promise>,
private basic_task_variant_result<typename Promise::result_type>
{
    using task_awaiter::basic_task_variant_result::result_index;
    using task_awaiter::basic_task_variant_result::exception_index;

    template<
        typename Result,
        is_continuation Continuation
    > friend class basic_task_promise;

    using typename task_awaiter::basic_task_variant_result::result_variant_type;
    result_variant_type m_result;

    bool has_exception(
    ) const noexcept
    {
        return m_result.index() == exception_index;
    }

    [[noreturn]] 
    void resume_exception(
    )
    {
        std::rethrow_exception(
            std::move(
                get<exception_index>(
                    m_result))
        );
    }

public:
    task_awaiter(
        task_awaitable<Promise>&& other
    ) : task_awaitable<Promise>(std::move(other))
    {}

    bool await_ready(
    ) const noexcept
    {
        return false;
    }

    auto await_suspend(
        auto awaiter
    ) noexcept
    {
        this->promise().continuation() = awaiter;
        this->promise().m_result = &m_result;
        return this->handle();
    }

    decltype(auto) await_resume(
    )
    {
        return this->await_resume_value(
            [&]() -> decltype(auto)
            {
                return this->resume_variant_result<result_index>(
                    m_result);
            });
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
        scope_guard destroyer = [&]()
        {
            this->handle().destroy();
            this->handle() = nullptr;
        };

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
> class basic_task
    :
    public task_awaitable<Promise>
{
public:
    using task_awaitable<Promise>::task_awaitable;
    using promise_type = Promise;

    basic_task()
    {}

    auto operator co_await(
        this std::movable auto && self
        )
    {
        return task_awaiter<Promise>
        {
            std::move(self),
        };
    }
};

template<
    typename Promise
> basic_task(coroutine_handle<Promise>) -> basic_task<Promise>;

}

namespace Phantom::Coroutines
{
using detail::basic_task;
using detail::basic_task_promise;
using detail::task;
using detail::task_promise;

}
