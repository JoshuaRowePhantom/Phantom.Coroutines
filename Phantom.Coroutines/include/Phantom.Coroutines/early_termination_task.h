#pragma once

#include "Phantom.Coroutines/type_traits.h"
#include <concepts>
#include <exception>
#include <type_traits>

namespace Phantom::Coroutines
{
namespace detail
{
template<
    typename Traits
> concept early_termination_traits = true;

template<
    early_termination_traits Traits
> class basic_early_termination_task;

template<
    typename Task
> concept is_early_termination_task =
is_template_instantiation<Task, basic_early_termination_task>;

template<
    typename T
> class early_termination_result;

template<
    typename T
> concept is_early_termination_result =
is_template_instantiation<T, early_termination_result>;

template<
    early_termination_traits Traits
> class basic_early_termination_promise;

template<
    typename Promise
> concept is_early_termination_promise
= is_template_instantiation<Promise, basic_early_termination_promise>;

template<
    typename Transformer,
    typename Promise
> concept is_early_termination_await_transformer
= std::convertible_to<Transformer, Promise>
&& is_early_termination_promise<Promise>;

template<
    is_early_termination_promise Promise
> class basic_early_termination_awaiter;

template<
    is_early_termination_task Task
> class basic_early_termination_task_awaiter;

template<
    is_early_termination_promise Promise
> class basic_early_termination_transformed_awaiter;

template<
    is_early_termination_promise Promise
> class basic_early_termination_task_await_transformer;

template<
    is_early_termination_promise CallingPromise,
    is_early_termination_task Task
> class basic_early_termination_transformed_task_awaiter;

template<
    is_early_termination_promise Promise
> class basic_early_termination_final_suspend_awaiter;

// The basic_early_termination_task_awaiter is returned
// by operator co_await of basic_early_termination_task, and provides
// the behavior of co_await'ing a basic_early_termination_task
// outside of another basic_early_termination_promise.
// This is the point of interoperation with ordinary caller co-routines.
template<
    is_early_termination_task Task
> class basic_early_termination_task_awaiter
{
    template<
        early_termination_traits Traits
    > friend class basic_early_termination_task;

    Task& m_task;

    basic_early_termination_task_awaiter(
        Task& task
    )
    {}

public:

};

// An early_termination_task converts exceptions and
// special returns into an early termination of the current coroutine
// and a resumption of an error-handling coroutine.
// If the caller was not an early_termination_task,
// the exception or special return is converted back into
// a rethrown exception in that caller.
// The underlying exception of a called can be obtained
// from an early_termination_task coroutine by using
// the handle_error() function.
template<
    early_termination_traits Traits
> class basic_early_termination_task
{
public:
    auto operator co_await() && noexcept
    {
        return basic_early_termination_task_awaiter{ *this };
    }
};

template<
    typename T
> class early_termination_result
{
    T m_value;
public:
    template<
        typename ... Args
    > early_termination_result(
        Args&&... args
    ) :
        m_value(std::forward<Args>(args)...)
    {
    }
};

// The basic_early_termination_final_suspend_awaiter transfers control
// to the correct calling coroutine after a promise has completed.
template<
    is_early_termination_promise Promise
> class basic_early_termination_final_suspend_awaiter
{
    template<
        early_termination_traits Traits
    > friend class basic_early_termination_promise;

    Promise& m_promise;

    basic_early_termination_final_suspend_awaiter(
        Promise& promise
    ) :
        m_promise(promise)
    {}

public:
    bool await_ready() const noexcept
    {
        return false;
    }

    coroutine_handle<> await_suspend(
        coroutine_handle<>
    )
    {
        return m_promise.resume();
    }

    [[noreturn]]
    void await_resume() const noexcept
    {
        std::terminate();
    }
};

// basic_early_termination_promise provides the early
// termination behavior for basic_early_termination_task.
template<
    early_termination_traits Traits
> class basic_early_termination_promise
{
public:
    // Choose the correct coroutine to resume.
    // The caller can resume the coroutine by
    // symmetric transfer or by a call to resume().
    coroutine_handle<> resume() noexcept
    {
    }

    template<
        typename T
    > void return_value(
        T&& result
    ) noexcept(std::is_nothrow_move_constructible_v<T>)
    {
    }

    void unhandled_exception() noexcept
    {
        return_value(
            early_termination_result
            {
                std::current_exception()
            }
        );
    }

    std::suspend_always initial_suspend() const noexcept
    {
        return {};
    }

    auto final_suspend() const noexcept
    {
        return basic_early_termination_final_suspend_awaiter{ *this };
    }
};

// The basic_early_termination_transformed_awaiter is the base
// class for awaiters of arbitrary types within the early return
// framework, including the basic_early_termination_transformed_task_awaiter.
// Derived classes can call set_result to set the result of the awaiter,
// including an early_termination_result. Then, the derived
// class can use resume() to obtain the coroutine_handle to result.
// The derived class can resume the coroutine_handle either by
// symmetric transfer or directly calling resume().
template<
    is_early_termination_promise CallingPromise
> class basic_early_termination_transformed_awaiter
{
    CallingPromise& m_promise;

protected:
    template<
        is_early_termination_await_transformer<CallingPromise> AwaitTransformer
    >
    basic_early_termination_transformed_awaiter(
        AwaitTransformer& transformer
    ) noexcept
        : m_promise(static_cast<CallingPromise&>(transformer))
    {
    }

    template<
        typename T
    > void return_value(
        T&& result
    ) noexcept(std::is_nothrow_move_constructible_v<T>)
    {
        return m_promise.return_value(
            std::forward<T>(result)
        );
    }

    coroutine_handle<> resume() noexcept
    {
        return m_promise.resume();
    }
};

template<
    is_early_termination_promise CallingPromise,
    is_early_termination_task Task
> class basic_early_termination_transformed_task_awaiter
    :
public basic_early_termination_transformed_awaiter<
    CallingPromise
>
{
    template<
        is_early_termination_promise Promise
    > friend class basic_early_termination_task_await_transformer;

    template<
        is_early_termination_await_transformer<CallingPromise> AwaitTransformer
    > basic_early_termination_transformed_task_awaiter(
        AwaitTransformer& transformer,
        Task&& task
    ) :
        basic_early_termination_transformed_awaiter<CallingPromise>(transformer)
    {}

public:
};

template<
    is_early_termination_promise Promise
> class basic_early_termination_task_await_transformer
{
public:
    template<
        is_early_termination_task Task
    > decltype(auto) await_transform(
        Task&& awaitable
    )
    {
        return basic_early_termination_transformed_task_awaiter
        {
            *this,
            awaitable,
        };
    }
};

}
using detail::basic_early_termination_awaiter;
using detail::basic_early_termination_promise;
using detail::basic_early_termination_task;
using detail::is_early_termination_result;
using detail::is_early_termination_promise;
using detail::is_early_termination_await_transformer;
}