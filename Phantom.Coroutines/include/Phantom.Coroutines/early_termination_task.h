#pragma once

#include <concepts>
#include <exception>
#include <tuple>
#include <type_traits>
#include "await_all_await_transform.h"
#include "detail/final_suspend_transfer.h"
#include "detail/variant_result_storage.h"
#include "extensible_promise.h"
#include "task.h"
#include "type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

class early_termination_policy
{};

class early_termination_transformer
    :
    public early_termination_policy
{};

class early_termination_result
    :
    public early_termination_policy
{};

template<
    typename Promise
>
class early_termination_awaiter
    :
    public early_termination_policy,
    public extensible_awaitable<Promise>
{
protected:
    auto error_handling_continuation(
        this auto& self
    ) noexcept
    {
        return self.promise().m_errorHandlingContinuation;
    }

public:
    early_termination_awaiter(
        Promise& promise
    ) noexcept :
        early_termination_awaiter::extensible_awaitable(promise)
    {}
};

template<
    typename Promise
>
class early_termination_synchronous_awaiter;

template<
    typename Awaiter
> concept is_early_termination_synchronous_awaiter = requires (Awaiter awaiter)
{
    { awaiter.is_error() } -> std::same_as<bool>;
    { awaiter.return_value() };
    { awaiter.await_resume() };
};

template<
    typename Promise
>
class early_termination_synchronous_awaiter
    :
    public early_termination_awaiter<Promise>
{
public:
    early_termination_synchronous_awaiter(
        Promise& promise
    ) noexcept :
        early_termination_synchronous_awaiter::early_termination_awaiter(promise)
    {}

    bool await_ready(
        this auto& self
    ) noexcept(noexcept(self.is_error()))
    {
        static_assert(is_early_termination_synchronous_awaiter<decltype(self)>);
        return !self.is_error();
    }

    auto await_suspend(
        this auto& self,
        // We ignore the continuation, because we will
        // resume the error handling continuation directly.
        auto&& continuation
    ) noexcept
    {
        static_assert(is_early_termination_synchronous_awaiter<decltype(self)>);
        
        continuation.promise().return_value(
            self.return_value()
        );

        // This method is only called if is_error() was true,
        // so it represents an error situation.
        // We should resume the error-handling continuation of the promise.
        return self.error_handling_continuation();
    }
};

template<
    typename Policy
> concept is_early_termination_policy = std::derived_from<Policy, early_termination_policy>;

template<
    typename Policy
> struct early_termination_policy_selector
:
    std::integral_constant<
        bool,
        is_early_termination_policy<Policy>
    >
{};

template<
    typename Policy
> concept is_early_termination_transformer = std::derived_from<Policy, early_termination_transformer>;

template<
    typename Policy
> struct early_termination_transformer_selector
:
    std::integral_constant<
        bool,
        is_early_termination_transformer<Policy>
    >
{};

// This class is returned from the co_await
// operator of basic_early_termination_task.
// It is noticeably NOT an awaiter.
// It is turned into an awaiter in the await_transform method of basic_early_termination_promise,
// or by the handle_errors() method.
template<
    typename Promise
> class basic_early_termination_task_co_await_operation
    :
    public task_awaitable<Promise>
{
    template<
        typename ErrorResult,
        typename Continuation
    > friend class basic_early_termination_promise;

public:
    basic_early_termination_task_co_await_operation(
        task_awaitable<Promise>&& other
    ) : task_awaitable<Promise>{ std::move(other) }
    {}

    void doassert()
    {
        static_assert(always_false<Promise>, "Cannot co_await an early_termination_task except by calling handle_errors() or inside a early_termination_task coroutine.");
    }

    // Implement the awaiter methods so that we can emit a useful static_assert message.
    void await_ready()
    {
        doassert();
    }

    void await_suspend(auto)
    {
        doassert();
    }

    void await_resume()
    {
        doassert();
    }
};

template<
    typename Promise
> class basic_early_termination_task
    :
public basic_task<Promise>
{
public:
    basic_early_termination_task(
        coroutine_handle<Promise> promise
    ) : basic_early_termination_task::basic_task{ promise }
    {}

    using basic_early_termination_task::basic_task::basic_task;

    auto operator co_await (
        this std::movable auto&& self
        ) noexcept
    {
        return basic_early_termination_task_co_await_operation<Promise>
        {
            std::move(self),
        };
    }

    auto handle_errors(
        this auto&& self
    ) noexcept
    {
        return task_awaiter
        {
            std::move(self)
        };
    }
};

template<
    typename ErrorResult,
    typename Continuation
> class basic_early_termination_promise
    :
    public basic_task_promise<ErrorResult, Continuation>,
    public await_all_await_transform
{
    template<
        typename Promise
    > friend class early_termination_awaiter;

    template<
        typename Promise
    > class non_error_handling_awaiter
        :
    public task_awaiter<Promise>
    {
        friend class basic_early_termination_promise;

        using non_error_handling_awaiter::task_awaitable::task_awaitable;
    };

    Continuation m_errorHandlingContinuation;

public:
    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return basic_early_termination_task{ self.handle() };
    }

    void unhandled_exception(
        this auto& self
    ) noexcept
    {
        self.m_continuation = self.m_errorHandlingContinuation;
        self.basic_early_termination_promise::basic_task_promise::unhandled_exception();
    }

    using await_all_await_transform::await_transform;

    // For early termination task awaiters that have specified not to handle errors,
    // return an awaiter that performs all the special logic of an early termination promise.
    template<
        typename Promise
    > auto await_transform(
        basic_early_termination_task_co_await_operation<Promise>&& operation
    ) noexcept
    {
        return non_error_handling_awaiter
        {
            std::move(operation),
        };
    }

    using basic_early_termination_promise::basic_task_promise::await_ready;

    // Suspend error-handling awaiters.
    template<
        std::derived_from<basic_early_termination_promise> Promise
    >
    auto await_suspend(
        this Promise& self,
        task_awaiter<Promise>& awaiter,
        auto continuation
    )
    {
        // Use the continuation for this awaiter as the error handling.
        self.m_errorHandlingContinuation = continuation;

        return self.basic_early_termination_promise::basic_task_promise::await_suspend(
            awaiter,
            continuation
        );
    }

    // Suspend non-error-handling awaiters
    template<
        std::derived_from<basic_early_termination_promise> Promise
    >
    auto await_suspend(
        this Promise& self,
        non_error_handling_awaiter<Promise>& nonErrorHandlingAwaiter,
        auto continuation
    )
    {
        // Use the error handling continuation of the promise associated
        // with the non-error-handling continuation.
        // continuation is guaranteed to be the coroutine handle of a basic_early_termination_promise.
        self.m_errorHandlingContinuation = continuation.promise().m_errorHandlingContinuation;

        return self.basic_early_termination_promise::basic_task_promise::await_suspend(
            nonErrorHandlingAwaiter,
            continuation
        );
    }

    // Resume error-handling awaiters.
    template<
        std::derived_from<basic_early_termination_promise> Promise
    >
    decltype(auto) await_resume(
        this Promise& self,
        task_awaiter<Promise>& awaiter
    )
    {
        return self.basic_early_termination_promise::basic_task_promise::await_resume(
            awaiter);
    }

    // Resume non-error-handling awaiters.
    template<
        std::derived_from<basic_early_termination_promise> Promise
    >
    decltype(auto) await_resume(
        this Promise& self,
        non_error_handling_awaiter<Promise>& awaiter
    )
    {
        // The task is guaranteed to have succeeded,
        // otherwise we would have resumed an error-handling awaiter.
        // Transform the result into the final result type.
        return self.return_result(
            std::move(get<self.result_index>(self.m_result))
        );
    }
};

template<
    typename Promise
> constexpr bool is_early_termination_promise_v = false;

template<
    typename Promise
> concept is_early_termination_promise =
is_template_instantiation<Promise, basic_early_termination_promise>;

template<
    is_template_instantiation<basic_early_termination_promise> Promise,
    is_template_instantiation<std::tuple> PoliciesTuple,
    is_template_instantiation<std::tuple> TransformerTypesTuple =
        typename filter_tuple_types<
            early_termination_transformer_selector,
            PoliciesTuple
        >::tuple_type
>
class early_termination_promise_inheritor;

template<
    typename Promise,
    typename ... Policies,
    typename ... Transformers
>
class early_termination_promise_inheritor<
    Promise,
    std::tuple<Policies...>,
    std::tuple<Transformers...>
> :
    public Policies...,
    public Promise
{
public:
    using Transformers::await_transform...;
};

template<
    typename ErrorResult,
    typename ... Policies
> using early_termination_promise = 
    early_termination_promise_inheritor<
        basic_early_termination_promise
        <
            ErrorResult,
            select_continuation_type<Policies..., default_continuation_type>
        >,
        typename filter_types<
            early_termination_policy_selector,
            Policies...
        >::tuple_type
    >;

template<
    typename ErrorResult,
    typename ... Policies
> using early_termination_task =
    basic_early_termination_task<
        early_termination_promise<
            ErrorResult,
            Policies...
        >
    >;
}

using detail::is_early_termination_policy;
using detail::early_termination_task;
using detail::early_termination_promise;
using detail::early_termination_transformer;
using detail::early_termination_awaiter;
using detail::early_termination_synchronous_awaiter;
using detail::early_termination_result;
}
