#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/promise_traits.h"
#include "single_consumer_promise.h"
#include <concepts>
#include <exception>
#include <type_traits>
#include <variant>

namespace Phantom::Coroutines
{
namespace detail
{
template<
    typename TResult = void
> class task;

template<
    typename TResult
>
class task_promise;

template<
    typename TResult
>
class task_promise_base
{
    template<
        typename TResult
    > friend class task;

protected:
    task<TResult>* m_task;

public:
    ~task_promise_base()
    {

    }
    suspend_always initial_suspend() const noexcept { return suspend_always{}; }
    
    inline final_suspend_transfer_and_destroy final_suspend() noexcept;
    inline task<TResult> get_return_object();
    inline void unhandled_exception() noexcept;
};

template<
    typename TResult
>
class task_promise
    :
public task_promise_base<TResult>
{
    template<
        typename TResult
    > friend class task;

    using task_promise::task_promise_base::m_task;
public:
    template<
        typename TValue
    > void return_value(
        TValue&& result
    )
    {
        m_task->m_result.emplace<task::value_index>(
            std::forward<TValue>(result)
            );
    }
};

template<
>
class task_promise<
    void
> :
public task_promise_base<void>
{
    template<
        typename TResult
    > friend class task;

    using task_promise::task_promise_base::m_task;
public:
    inline void return_void();
};

template<
    typename TResult
>
class task
{
    template<
        typename TResult
    > friend class task_promise;

    template<
        typename TResult
    > friend class task_promise_base;
public:
    typedef task_promise<TResult> promise_type;
private:
    typedef std::conditional_t<
        std::is_same_v<void, TResult>,
        std::monostate,
        TResult
    > result_variant_member_type;

    typedef std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    const static size_t value_index = 1;
    const static size_t exception_index = 2;

    result_variant_type m_result;

    promise_type* m_promise = nullptr;
    coroutine_handle<> m_continuation;

    task(
        promise_type* promise
    ) : m_promise(
        promise
    )
    {
    }

    task(
        task&&
    ) = delete;

    task(
        const task&
    ) = delete;

    void operator=(
        const task&
        ) = delete;

    void operator=(
        const task&&
        ) = delete;

    class awaiter
    {
        friend class task;
        task& m_task;

        awaiter(
            task& task
        ) :
            m_task{ task }
        {}

    public:
        bool await_ready() { return false; }

        coroutine_handle<> await_suspend(
            coroutine_handle<> continuation
        )
        {
            m_task.m_continuation = continuation;
            m_task.m_promise->m_task = &m_task;
            return coroutine_handle<task_promise<TResult>>::from_promise(*m_task.m_promise);
        }

        auto await_resume()
        {
            if (m_task.m_result.index() == exception_index)
            {
                std::rethrow_exception(
                    get<exception_index>(m_task.m_result));
            }

            if constexpr (std::is_same_v<TResult, void>)
            {
                return;
            }
            else
            {
                return (std::get<value_index>(m_task.m_result));
            }
        }
    };
public:
    awaiter operator co_await()
    {
        return awaiter{ *this };
    }
};

template<
    typename TResult
> task<TResult>
task_promise_base<TResult>::get_return_object()
{
    return task<TResult>{ static_cast<task_promise<TResult>*>(this) };
}

template<
    typename TResult
> final_suspend_transfer_and_destroy
task_promise_base<TResult>::final_suspend() noexcept
{
    return final_suspend_transfer_and_destroy
    {
        m_task->m_continuation
    };
}

template<
    typename TResult
>
void task_promise_base<TResult>::unhandled_exception() noexcept
{
    m_task->m_result.emplace<task<TResult>::exception_index>(
        std::current_exception()
        );
}
void task_promise<void>::return_void()
{
    m_task->m_result.emplace<task<void>::value_index>(std::monostate{});
}

}
using detail::task;

}