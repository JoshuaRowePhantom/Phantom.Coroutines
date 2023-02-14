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
#include "policies.h"
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
{
    struct invalid_return_value {};
public:
    void get_error_result(invalid_return_value);
    void get_success_value(invalid_return_value);
};

class early_termination_error_propagator
{
public:
    // Propagate the error to some caller.
    // Return the coroutine handle of the coroutine
    // to resume.
    // This coroutine handle may be the result of 
    // early_termination_error_propagator::propagate_error
    virtual coroutine_handle<> propagate_error() = 0;

    // Propagate the exception to some caller.
    // Return the coroutine handle of the coroutine
    // to resume.
    // This coroutine handle may be the result of 
    // early_termination_error_propagator::propagate_error
    virtual coroutine_handle<> propagate_exception() = 0;
};

class early_termination_exception_sink
{
public:
    // Propagate the currently unhandled exception to the error handling awaiter.
    // Return the coroutine handle of the coroutine
    // to resume.
    virtual void return_unhandled_exception() = 0;
};

template<
    typename ErrorResult
>
class early_termination_result_sink
    :
    public early_termination_error_propagator
{
public:
    virtual void return_value(
        ErrorResult&& errorResult
    ) = 0;
};

class early_termination_error_propagator_loop
{
    template<
        typename CallingPromise,
        typename CalledPromise
    > friend class basic_non_error_handling_early_termination_task_awaiter;

public:
    class promise_type
    {
        friend class early_termination_error_propagator_loop;

        // The error propagator to invoke next.
        // This is set by propagate_error() and propagate_exception().
        early_termination_error_propagator* m_nextErrorPropagator;
        // The function to invoke on the error propagator.
        // This is set by propagate_error() and propagate_exception().
        coroutine_handle<>(early_termination_error_propagator::* m_nextErrorPropagatorFunction)();

    public:
        auto get_return_object()
        {
            return early_termination_error_propagator_loop{ *this };
        }

        suspend_always initial_suspend() const noexcept
        {
            return {};
        }

        [[noreturn]]
        suspend_never final_suspend() const noexcept
        {
            // This should never be called, because the error propagator
            // loop should run forever.
            std::terminate();
        }

        [[noreturn]]
        void unhandled_exception() const noexcept
        {
            // This should never be called, because the error propagator
            // loop should run forever.
            std::terminate();
        }

        [[noreturn]]
        void return_void() const noexcept
        {
            // This should never be called, because the error propagator
            // loop should run forever.
            std::terminate();
        }
    };

    // Propagate an error using the current thread-local error reporter,
    // resuming the coroutine returned by the error reporter.
    class propagate_early_termination_awaiter
    {
    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        coroutine_handle<> await_suspend(
            coroutine_handle<promise_type> propagator
        ) const noexcept
        {
            auto& promise = propagator.promise();
            return (promise.m_nextErrorPropagator->*promise.m_nextErrorPropagatorFunction)();
        }

        void await_resume() const noexcept
        {
        }
    };

private:
    promise_type& m_promise;

    early_termination_error_propagator_loop(
        promise_type& promise
    ) : m_promise{ promise }
    {
    }

    static thread_local early_termination_error_propagator_loop t_errorPropagatorLoop;

    static early_termination_error_propagator_loop do_propagation_loop()
    {
        while (true)
        {
            co_await propagate_early_termination_awaiter{};
        }
    }

    // Obtain a thread-local coroutine handle to resume in order to
    // propagate an error using the passed-in errorReporter.
    // The returned coroutine will be an instance of early_termination_error_propagator_loop(),
    // which will then simply resume the correct coroutine.
    static coroutine_handle<> propagate_error(
        early_termination_error_propagator* errorPropagator)
    {
        t_errorPropagatorLoop.m_promise.m_nextErrorPropagator = errorPropagator;
        t_errorPropagatorLoop.m_promise.m_nextErrorPropagatorFunction = &early_termination_error_propagator::propagate_error;

        return coroutine_handle<promise_type>::from_promise(
            t_errorPropagatorLoop.m_promise
        );
    }

    // Obtain a thread-local coroutine handle to resume in order to
    // propagate an exception using the passed-in errorReporter.
    // The returned coroutine will be an instance of early_termination_error_propagator_loop(),
    // which will then simply resume the correct coroutine.
    static coroutine_handle<> propagate_exception(
        early_termination_error_propagator* errorPropagator)
    {
        t_errorPropagatorLoop.m_promise.m_nextErrorPropagator = errorPropagator;
        t_errorPropagatorLoop.m_promise.m_nextErrorPropagatorFunction = &early_termination_error_propagator::propagate_exception;

        return coroutine_handle<promise_type>::from_promise(
            t_errorPropagatorLoop.m_promise
        );
    }};

inline thread_local early_termination_error_propagator_loop early_termination_error_propagator_loop::t_errorPropagatorLoop 
    = early_termination_error_propagator_loop::do_propagation_loop();

// An early_termination_transformed_awaiter can cause a promise to terminate early.
template<
    typename Promise
>
class early_termination_awaiter
    :
    public early_termination_policy,
    public extensible_promise_handle<Promise>
{
protected:
    auto return_error_value(
        this auto& self,
        auto&& value
    )
    {
        self.promise().return_error_value(
            std::forward<decltype(value)>(value));
        return self.promise().continuation();
    }

public:
    early_termination_awaiter(
        Promise& promise
    ) noexcept :
        early_termination_awaiter::extensible_promise_handle(promise)
    {}
};

template<
    typename Promise
>
class early_termination_synchronous_awaiter;

template<
    typename Awaiter
> concept is_early_termination_synchronous_awaiter = 
is_derived_instantiation<Awaiter, early_termination_synchronous_awaiter>
&& requires (Awaiter awaiter)
{
    { awaiter.is_error() } -> std::same_as<bool>;
    // Implemented by a early_termination_synchronous_awaiter derived class to get
    // the awaited value in an error handling context.
    { awaiter.get_error_result() };
    // Implemented by a early_termination_synchronous_awaiter derived class to return
    // the awaited value in a non-error handling context.
    { awaiter.await_resume() };
};

// early_termination_synchronous_awaiter provides a framework for awaiting
// synchronously-obtained values.
// Derived classes must implement the is_early_termination_synchronous_awaiter
// concept.
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
        
        // This method is only called if is_error() was true,
        // so it represents an error situation.
        // We should resume the error-handling continuation of the promise.
        return self.return_error_value(
            self.get_error_result()
        );
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

template<
    typename Policy
> concept is_early_termination_result = std::derived_from<Policy, early_termination_result>;

template<
    typename Policy
> struct early_termination_result_selector
    :
    std::integral_constant<
        bool,
        is_early_termination_result<Policy>
    >
{};

// This awaiter is used to capture and return the successful or error result of
// executing an early_termination_task.
template<
    typename ResultType
> struct basic_error_handling_early_termination_task_result
{
    using variant_result_storage = variant_result_storage<ResultType>;
    using result_variant_member_type = typename variant_result_storage::result_variant_member_type;
    using variant_type = std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    >;
};

template<
    typename CalledPromise
> class basic_error_handling_early_termination_task_awaiter
    :
    public single_owner_promise_handle<CalledPromise>,
    private early_termination_exception_sink,
    private early_termination_result_sink<typename CalledPromise::result_type>
{
    template<
        typename BasePromise
    > friend class basic_early_termination_promise;

    using result_type = typename CalledPromise::result_type;
    using variant_result = basic_error_handling_early_termination_task_result<result_type>;
    using variant_result_storage = typename variant_result::variant_result_storage;
    using result_variant_member_type = typename variant_result::result_variant_member_type;
    using variant_type = typename variant_result::variant_type;
    
    static constexpr size_t result_index = 1;
    static constexpr size_t exception_index = 2;

    variant_type m_result;

    // An error_handling awaiter should always continue the coroutine
    // that is awaiting it.
    virtual coroutine_handle<> propagate_error() override
    {
        return this->promise().continuation();
    }

    // An error_handling awaiter should always continue the coroutine
    // that is awaiting it.
    virtual coroutine_handle<> propagate_exception() override
    {
        return this->promise().continuation();
    }

    // Propagate the exception to awaiting coroutine.
    virtual void return_unhandled_exception() override
    {
        this->m_result.emplace<exception_index>(
            std::current_exception());
    }

    virtual void return_value(
        result_type&& result
    ) override
    {
        m_result.emplace<result_index>(
            std::forward<result_type>(result));
    }

public:
    basic_error_handling_early_termination_task_awaiter(
        single_owner_promise_handle<CalledPromise>&& task
    ) :
        single_owner_promise_handle<CalledPromise>(std::move(task))
    {
    }

    bool await_ready() const noexcept
    {
        return false;
    }

    auto await_suspend(
        auto continuation
    )
    {
        this->promise().continuation() = continuation;
        this->promise().m_resultSink = this;
        this->promise().m_exceptionSink = this;
        return this->handle();
    }

    decltype(auto) await_resume(
        this auto& self
    )
    {
        auto destroyer = self.destroy_on_scope_exit();

        if (self.m_result.index() == exception_index)
        {
            std::rethrow_exception(
                get<exception_index>(self.m_result));
        }

        return variant_result_storage::resume_variant_result<result_index>(
            self.m_result);
    }
};

template<
    typename CallingPromise,
    typename CalledPromise
> class basic_non_error_handling_early_termination_task_awaiter
    :
    public single_owner_promise_handle<CalledPromise>,
    public early_termination_result_sink<typename CalledPromise::result_type>
{
    template<
        typename BasePromise
    > friend class basic_early_termination_promise;

    using result_type = typename CalledPromise::result_type;
    using variant_result = basic_error_handling_early_termination_task_result<result_type>;
    using variant_result_storage = typename variant_result::variant_result_storage;
    using result_variant_member_type = typename variant_result::result_variant_member_type;
    using variant_type = typename variant_result::variant_type;

    static constexpr size_t result_index = 1;

    variant_type m_result;
    coroutine_handle<CallingPromise> m_continuation;

    basic_non_error_handling_early_termination_task_awaiter(
        single_owner_promise_handle<CalledPromise>&& task
    ) : 
        single_owner_promise_handle<CalledPromise> { std::move(task) }
    {}

    // An error_handling awaiter should always continue the coroutine
    // that is awaiting it.
    virtual coroutine_handle<> propagate_error() override
    {
        m_continuation.promise().return_error_value(
            variant_result_storage::template resume_variant_result<result_index>(
                m_result));

        return early_termination_error_propagator_loop::propagate_error(
            m_continuation.promise().m_resultSink);
    }

    // An error_handling awaiter should always continue the coroutine
    // that is awaiting it.
    virtual coroutine_handle<> propagate_exception() override
    {
        return early_termination_error_propagator_loop::propagate_exception(
            m_continuation.promise().m_resultSink);
    }

    virtual void return_value(
        typename CalledPromise::result_type&& value
    ) override
    {
        m_result.emplace<result_index>(
            std::forward<decltype(value)>(value));
    }

public:
    bool await_ready() const noexcept
    {
        return false;
    }

    auto await_suspend(
        // continuation is guaranteed to be an std::coroutine_handle<> of a basic_early_termination_promise.
        auto continuation
    )
    {
        this->m_continuation = continuation;
        this->promise().continuation() = continuation;
        this->promise().m_resultSink = this;
        this->promise().m_exceptionSink = continuation.promise().m_exceptionSink;
        return this->handle();
    }

    decltype(auto) await_resume(
        this auto&& self
    )
    {
        auto destroyer = self.destroy_on_scope_exit();

        // The task is guaranteed to have succeeded,
        // otherwise we would have resumed an error-handling awaiter.
        // Transform the result into the final result type.
        return self.promise().get_success_value(
            variant_result_storage::template resume_variant_result<result_index>(
                std::forward<decltype(self)>(self).m_result));
    }
};

template<
    typename Promise
> class basic_early_termination_task
    :
public single_owner_promise_handle<Promise>
{
public:
    using basic_early_termination_task::single_owner_promise_handle::single_owner_promise_handle;

    void operator co_await(
        this std::movable auto&& self
        ) noexcept
    {
        static_assert(
            always_false<Promise>,
            "Cannot co_await an early_termination_task except using handle_errors() or inside an early_termination_task.");
    }

    auto handle_errors(
        this auto&& self
    ) noexcept
    {
        return basic_error_handling_early_termination_task_awaiter<Promise>
        {
            std::move(self)
        };
    }
};

template<
    typename Promise
> basic_early_termination_task(coroutine_handle<Promise>) -> basic_early_termination_task<Promise>;

template<
    typename BasePromise
> class basic_early_termination_promise
    :
    public derived_promise<BasePromise>,
    public await_all_await_transform
{
public:
    using typename basic_early_termination_promise::derived_promise::result_type;

private:
    template<
        typename BasePromise
    > friend class basic_early_termination_promise;

    template<
        typename Promise
    > friend class early_termination_awaiter;

    template<
        typename Promise
    > friend class basic_error_handling_early_termination_task_awaiter;

    template<
        typename CallingPromise,
        typename CalledPromise
    > friend class basic_non_error_handling_early_termination_task_awaiter;

    early_termination_exception_sink* m_exceptionSink;
    early_termination_result_sink<result_type>* m_resultSink;

public:
    void return_error_value(
        this auto& self,
        auto&& value
    )
    {
        self.basic_early_termination_promise::m_resultSink->return_value(
            self.get_error_result<result_type>(
                std::forward<decltype(value)>(value)));
        self.basic_early_termination_promise::continuation() = self.basic_early_termination_promise::m_resultSink->propagate_error();
    }

    void return_result_value(
        this auto& self,
        auto&& value
    )
    {
        if (self.is_error_value(value))
        {
            self.return_error_value(
                std::forward<decltype(value)>(value));
        }
        else
        {
            self.basic_early_termination_promise::m_resultSink->return_value(
                self.get_result_value(
                    std::forward<decltype(value)>(value)));
        }
    }

    void return_value(
        this auto& self,
        result_type& value
    )
    {
        return self.return_result_value(
            value);
    }

    void return_value(
        this auto& self,
        result_type&& value
    )
    {
        return self.return_result_value(
            std::move(value));
    }

    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return basic_early_termination_task
        { 
            self.basic_early_termination_promise::handle() 
        };
    }

    void unhandled_exception(
        this auto& self
    ) noexcept
    {
        self.basic_early_termination_promise::m_exceptionSink->return_unhandled_exception();
        self.basic_early_termination_promise::continuation() =
            self.basic_early_termination_promise::m_resultSink->propagate_exception();
    }

    using await_all_await_transform::await_transform;

    // For early termination tasks that have specified not to handle errors,
    // return an awaiter that performs all the special logic of an early termination promise.
    template<
        typename Promise
    > auto await_transform(
        this auto& self,
        basic_early_termination_task<Promise>&& operation
    ) noexcept
    {
        return basic_non_error_handling_early_termination_task_awaiter<
            std::decay_t<decltype(self)>,
            Promise
        >
        {
            std::move(operation),
        };
    }
};

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
        >::tuple_type,
    is_template_instantiation<std::tuple> ResultTypesTuple =
        typename filter_tuple_types<
            early_termination_result_selector,
            PoliciesTuple
        >::tuple_type
>
class early_termination_promise_inheritor;

template<
    typename Promise,
    typename ... Policies,
    typename ... Transformers,
    typename ... Results
>
class early_termination_promise_inheritor<
    Promise,
    std::tuple<Policies...>,
    std::tuple<Transformers...>,
    std::tuple<Results...>
> :
    public Policies...,
    public Promise
{
public:
    using Transformers::await_transform...;
    using Results::get_success_value...;
    using Results::is_error_value...;
    using Results::get_error_result...;
    using Promise::return_error_value;
    using Promise::return_value;
    using Promise::await_transform;
};

template<
    typename ... Policies
> using early_termination_promise = 
    early_termination_promise_inheritor<
        basic_early_termination_promise
        <
            select_base_promise_type<Policies...>
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
    basic_early_termination_task
    <
        early_termination_promise
        <
            base_promise_type
            <
                task_promise<ErrorResult>
            >,
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
