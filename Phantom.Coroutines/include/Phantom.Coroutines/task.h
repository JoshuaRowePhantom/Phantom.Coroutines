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
    typename Traits
> concept TaskTraits = requires
{
    typename Traits::promise_type;
    typename Traits::future_type;
    typename Traits::result_type;
};

template<
    typename Traits
> concept VoidTaskTraits =
TaskTraits<Traits>
&&
std::same_as<void, typename Traits::result_type>;

template<
    typename Traits
> concept ReferenceTaskTraits =
TaskTraits<Traits>
&&
std::is_reference_v<typename Traits::result_type>;

template<
    typename TResult = void
> class task;

template<
    typename TResult = void
> class task_promise;

template<
    TaskTraits Traits
>
class basic_task_promise;

template<
    typename TResult
> struct task_traits
{
    typedef task_promise<TResult> promise_type;
    typedef task<TResult> future_type;
    typedef TResult result_type;
};

template<
    TaskTraits Traits
>
class basic_task_promise_base
{
    template<
        TaskTraits Traits
    > friend class basic_task;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

protected:
    future_type* m_task;

public:
    suspend_always initial_suspend() const noexcept { return suspend_always{}; }
    
    inline final_suspend_transfer_and_destroy final_suspend() noexcept;
    inline future_type get_return_object();
    inline void unhandled_exception() noexcept;
};

template<
    TaskTraits Traits
>
class basic_task_promise
    :
public basic_task_promise_base<Traits>
{
    template<
        TaskTraits Trait
    > friend class basic_task;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

    using basic_task_promise::basic_task_promise_base::m_task;

public:
    template<
        typename TValue
    > void return_value(
        TValue&& result
    )
    {
        m_task->m_result.emplace<future_type::value_index>(
            std::forward<TValue>(result)
            );
    }
};

template<
    VoidTaskTraits Traits
>
class basic_task_promise<
    Traits
> :
public basic_task_promise_base<Traits>
{
    template<
        TaskTraits Traits
    > friend class basic_task;

    using basic_task_promise::basic_task_promise_base::m_task;
public:
    inline void return_void();
};

template<
    TaskTraits Traits
> struct basic_task_result_type
{
    typedef Traits::result_type result_variant_member_type;
    static constexpr bool is_void = false;
};

template<
    VoidTaskTraits Traits
> struct basic_task_result_type<
    Traits
>
{
    typedef std::monostate result_variant_member_type;
    static constexpr bool is_void = true;
};

template<
    ReferenceTaskTraits Traits
> struct basic_task_result_type<
    Traits
>
{
    typedef std::reference_wrapper<std::remove_reference_t<typename Traits::result_type>> result_variant_member_type;
    static constexpr bool is_void = false;
};

template<
    TaskTraits Traits
> class basic_task
    :
private basic_task_result_type<Traits>
{
    using typename basic_task::basic_task_result_type::result_variant_member_type;
    using basic_task::basic_task_result_type::is_void;

    template<
        TaskTraits Traits
    > friend class basic_task_promise;

    template<
        TaskTraits Traits
    > friend class basic_task_promise_base;

    friend class task_test;
public:
    using promise_type = typename Traits::promise_type;
    using result_type = typename Traits::result_type;
    using future_type = typename Traits::future_type;
    
private:
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

    basic_task(
        promise_type* promise
    ) : m_promise(
        promise
    )
    {
    }

    basic_task(
        basic_task&&
    ) = delete;

    basic_task(
        const basic_task&
    ) = delete;

    void operator=(
        const basic_task&
        ) = delete;

    void operator=(
        const basic_task&&
        ) = delete;

    class awaiter
    {
        friend class basic_task;
        future_type& m_task;

        awaiter(
            future_type& task
        ) :
            m_task{ task }
        {}

    public:
        bool await_ready() { return false; }

        coroutine_handle<> await_suspend(
            coroutine_handle<> continuation
        )
        {
            // The task can only be co-awaited once.
            assert(!m_task.m_continuation);

            m_task.m_continuation = continuation;
            m_task.m_promise->m_task = &m_task;
            return coroutine_handle<promise_type>::from_promise(*m_task.m_promise);
        }

        decltype(auto) await_resume()
        {
            if (m_task.m_result.index() == exception_index)
            {
                std::rethrow_exception(
                    get<exception_index>(m_task.m_result));
            }

            if constexpr (is_void)
            {
                return;
            }
            else
            {
                return (static_cast<result_type>((std::get<value_index>(m_task.m_result))));
            }
        }
    };

public:
    awaiter operator co_await()
    {
        return awaiter{ static_cast<future_type&>(*this) };
    }
};

template<
    typename TResult
>
class task
    :
public basic_task<task_traits<TResult>>
{
};

template<
    typename TResult
> class task_promise
    :
public basic_task_promise<task_traits<TResult>>
{};

template<
    TaskTraits Traits
> typename Traits::future_type
basic_task_promise_base<Traits>::get_return_object()
{
    return future_type{ static_cast<promise_type *>(this) };
}

template<
    TaskTraits Traits
> final_suspend_transfer_and_destroy
basic_task_promise_base<Traits>::final_suspend() noexcept
{
    return final_suspend_transfer_and_destroy
    {
        m_task->m_continuation
    };
}

template<
    TaskTraits Traits
>
void basic_task_promise_base<Traits>::unhandled_exception() noexcept
{
    m_task->m_result.emplace<basic_task<Traits>::exception_index>(
        std::current_exception()
        );
}

template<
    VoidTaskTraits Traits
>
void basic_task_promise<Traits>::return_void()
{
    m_task->m_result.emplace<task<void>::value_index>(std::monostate{});
}

}
using detail::task;

}