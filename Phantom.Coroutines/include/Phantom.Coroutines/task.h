#pragma once

#include "detail/coroutine.h"
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
    > variant_member_type;

    typedef std::variant<
        variant_member_type,
        std::exception_ptr
    > promise_value_type;

    const size_t value_index = 0;
    const size_t exception_index = 1;

    class promise_type
    {
        friend class task;

        single_consumer_promise<promise_value_type> m_singleConsumerPromise;

        suspend_always initial_suspend() const { return suspend_always{}; }
        suspend_never final_suspend() const { return suspend_never{}; }
        task get_return_object() { return task{ *this }; }

        std::enable_if_t<std::same_as<TValue, void>> return_void()
        {
            m_singleConsumerPromise.emplace(
                std::in_place_index<value_index>,
                std::monostate
            );
        }

        template<
            typename TResult
        >
        std::enable_if_t<!std::same_as<TValue, void>> return_value(
            TResult&& result
        )
        {
            m_singleConsumerPromise.emplace(
                std::in_place_index<value_index>,
                std::forward<TResult>(result)
            );
        }

        void unhandled_exception()
        {
            m_singleConsumerPromise.emplace(
                std::in_place_index<exception_index>,
                std::current_exception()
            );
        }
    };

    promise_type* m_promise;

    task(
        promise_type* promise
    ) : m_promise(
        promise
    )
    {}

public:
    bool await_ready() { return m_promise->m_singleConsumerPromise.await_ready(); }
    
    bool await_suspend(
        coroutine_handle<> coroutine
    )
    {
        return m_promise->m_singleConsumerPromise.await_suspend(
            coroutine
        );
    }

    TValue& await_resume()
    {
        auto& value = m_promise->m_singleConsumerPromise.await_resume();
        
        if (value.index() == value_index)
        {
            return get<value_index>(value);
        }

        std::rethrow_exception(
            get<exception_index>(value));
    }
};

}
using detail::task;

}