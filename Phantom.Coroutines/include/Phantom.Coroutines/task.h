#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "detail/promise_traits.h"
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
> concept is_task_promise_policy =
is_continuation_type_policy<Policy>;

template<
    typename Result,
    is_task_promise_policy ... Policies
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
    typename Result = void
> using task = basic_task<task_promise<Result>>;

template<
    typename Promise
> class task_awaiter;

template<
    typename Result,
    is_continuation Continuation
> class basic_task_promise
    :
    public variant_return_result<Result>,
    public extensible_promise,
    private variant_result_storage<Result>
{
    using variant_result_storage<Result>::is_void;

    friend class basic_task<basic_task_promise>;

private:
    typedef std::variant<
        std::monostate,
        typename variant_result_storage<Result>::result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    result_variant_type m_result;
    static const size_t result_index = 1;
    static const size_t exception_index = 2;

    Continuation m_continuation;

protected:
    Continuation& continuation(
        this auto& self
    )
    {
        return self.m_continuation;
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
        return final_suspend_transfer{ self.m_continuation };
    }

    template<
        typename Self
    >
    auto get_return_object(
        this Self& self
    ) noexcept
    {
        return basic_task<Self>(
            self.handle()
            );
    }

    auto await_ready(
        this auto& self,
        auto& awaiter
    )
    {
        return false;
    }

    auto await_suspend(
        this auto& self,
        auto& awaiter,
        auto continuation
    )
    {
        self.continuation() = continuation;
        return self.handle();
    }

    bool has_exception(
        this auto& self
    ) noexcept
    {
        return self.m_result.index() == exception_index;
    }

    [[noreturn]] void rethrow_exception(
        this auto& self
    )
    {
        std::rethrow_exception(
            get<exception_index>(
                self.m_result)
        );
    }

    decltype(auto) await_resume(
        this auto& self,
        auto& awaiter
    )
    {
        if (self.has_exception())
        {
            self.rethrow_exception();
        }

        return self.return_successful_result();
    }

    decltype(auto) return_successful_result(
        this auto& self)
    {
        [[assume(self.m_result.index() == result_index)]];

        return self.variant_result_storage<Result>::return_result<result_index>(
            self.m_result);
    }

    decltype(auto) return_exception(
        this auto& self,
        std::exception_ptr exception)
    {
        self.m_result.emplace<exception_index>(
            std::move(exception));
    }

    void return_variant_result(
        this auto& self,
        auto&& value
    )
    {
        self.m_result.emplace<result_index>(
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
> class task_awaitable
    :
public extensible_awaitable<Promise>
{
public:
    task_awaitable(
    )
    {}

    task_awaitable(
        coroutine_handle<Promise> handle
    ) :
        extensible_awaitable<Promise>{ handle }
    {}

    task_awaitable(
        task_awaitable&& other
    ) :
        extensible_awaitable<Promise>{ std::move(other) }
    {
        other.handle() = nullptr;
    }
    
    task_awaitable& operator=(
        task_awaitable&& other
        )
    {
        if (this->handle())
        {
            this->handle().destroy();
        }
        this->handle() = other.handle();
        other.handle() = nullptr;
    }

    ~task_awaitable()
    {
        if (this->handle())
        {
            this->handle().destroy();
        }
    }
};

template<
    typename Promise
> class task_awaiter 
    :
public task_awaitable<Promise>
{
public:
    task_awaiter(
        task_awaitable<Promise>&& other
    ) : task_awaitable<Promise>(std::move(other))
    {}

    bool await_ready(
        this auto& self
    ) noexcept
    {
        return self.promise().await_ready(self);
    }

    auto await_suspend(
        this auto& self,
        auto awaiter
    ) noexcept
    {
        return self.promise().await_suspend(self, awaiter);
    }

    decltype(auto) await_resume(
        this auto& self
    )
    {
        return self.promise().await_resume(self);
    }
};

template<
    typename Promise
> class basic_task
    :
    public task_awaitable<Promise>
{
public:
    using basic_task::task_awaitable::task_awaitable;
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

}

namespace Phantom::Coroutines
{
using detail::basic_task;
using detail::basic_task_promise;
using detail::task;
using detail::task_promise;

}
