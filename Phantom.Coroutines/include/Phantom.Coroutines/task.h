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
    typename TValue
>
class task
{
    typedef std::conditional_t<
        std::is_same_v<void, TValue>,
        std::monostate,
        TValue
    > result_variant_member_type;

    typedef std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    const size_t value_index = 1;
    const size_t exception_index = 2;

    result_variant_type m_result;

    class promise_type
    {
        friend class task;

        task* m_task;

        suspend_always initial_suspend() const { return suspend_always{}; }
        auto final_suspend() const 
        {
            return final_suspend_transfer_and_destroy
            {
                *this,
                m_task->m_continuation
            };
        }

        task get_return_object() { return task{ this }; }

        std::enable_if_t<std::same_as<TValue, void>> return_void()
        {
        }

        template<
            typename TResult
        >
        std::enable_if_t<!std::same_as<TValue, void>> return_value(
            TResult&& result
        )
        {
            m_task->m_result.emplace<value_index>(
                std::forward<TResult>(result)
            );
        }

        void unhandled_exception()
        {
            m_task->m_result.emplace<exception_index>(
                std::current_exception()
            );
        }
    };

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

        bool await_suspend(
            coroutine_handle<> continuation
        )
        {
            m_task.m_continuation = continuation;
            m_task.m_promise->m_task = m_task;
            return true;
        }

        std::enable_if<!std::is_same_v<TValue, void>, TValue&> await_resume()
        {
            if (m_task.m_result.index() == value_index)
            {
                return get<value_index>(m_task.m_result);
            }

            std::rethrow_exception(
                get<exception_index>(m_task.m_result));
        }

        std::enable_if<std::is_same_v<TValue, void>> await_resume()
        {
            if (m_task.m_promise->m_result.index() == exception_index)
            {
                std::rethrow_exception(
                    get<exception_index>(m_task.m_result));
            }
        }
    };
public:
    awaiter operator co_await()
    {
        return awaiter{ *this };
    }
};

}
using detail::task;

}