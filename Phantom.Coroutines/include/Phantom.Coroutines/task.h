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

namespace Phantom::Coroutines
{
namespace detail
{

// The Traits parameter to basic_task, basic_task_promise must satisfy this concept.
template<
    typename Traits
> concept TaskTraits = requires
{
    // The basic_task_promise-derived class that implements the promise type.
    typename Traits::promise_type;

    // The basic_task-derived class that implements the future type.
    typename Traits::future_type;

    // The result type of the task.
    typename Traits::result_type;

    // The type of awaiter.
    typename Traits::awaiter_type;
};

// A specialization of TaskTraits to detect void-returning tasks.
template<
    typename Traits
> concept VoidTaskTraits =
TaskTraits<Traits>
&&
std::same_as<void, typename Traits::result_type>;

// A specialization of TaskTraits to detect reference-returning tasks.
template<
    typename Traits
> concept ReferenceTaskTraits =
TaskTraits<Traits>
&&
std::is_reference_v<typename Traits::result_type>;

template<
    TaskTraits Traits
>
class basic_task_promise;

template<
    TaskTraits Traits
> class basic_task_awaiter
    :
    private immovable_object,
    private variant_result_storage<typename Traits::result_type>
{
    template<
        TaskTraits Traits
    > friend class basic_task_promise;

    template<
        TaskTraits Traits
    > friend class basic_task_promise_base;

    using promise_type = typename Traits::promise_type;
    using result_type = typename Traits::result_type;
    using awaiter_type = typename Traits::awaiter_type;
    using future_type = typename Traits::future_type;

    using typename basic_task_awaiter::variant_result_storage::result_variant_member_type;
    using basic_task_awaiter::variant_result_storage::is_void;
    using basic_task_awaiter::variant_result_storage::is_reference;

    typedef std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    static const size_t value_index = 1;
    static const size_t exception_index = 2;

    result_variant_type m_result;

    promise_type* m_promise = nullptr;
    coroutine_handle<> m_continuation;

protected:
    basic_task_awaiter(
        future_type* future
    ) : m_promise(
        future->m_promise
    ) 
    {
        future->m_promise = nullptr;
    }

public:
    ~basic_task_awaiter()
    {
        if (m_promise)
        {
            coroutine_handle<promise_type>::from_promise(*m_promise).destroy();
        }
    }

    bool await_ready() const
    {
        return false;
    }

    coroutine_handle<> await_suspend(
        coroutine_handle<> continuation
    )
    {
        m_promise->m_awaiter = static_cast<awaiter_type*>(this);
        m_continuation = continuation;

        return coroutine_handle<promise_type>::from_promise(*m_promise);
    }

    decltype(auto) await_resume()
    {
        if (m_result.index() == exception_index)
        {
            std::rethrow_exception(
                get<exception_index>(m_result));
        }
        
        return static_cast<
            std::add_rvalue_reference_t<
                basic_task_awaiter::variant_result_storage::result_type
            >
        >(
            basic_task_awaiter::variant_result_storage::get<value_index>(
                m_result
                )
            );
    }
};

template<
    TaskTraits Traits
>
class basic_task_promise_base
    :
private immovable_object
{
    template<
        TaskTraits Traits
    > friend class basic_task_awaiter;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;
    using awaiter_type = typename Traits::awaiter_type;
    using basic_task_awaiter_type = typename basic_task_awaiter<Traits>;

protected:
    awaiter_type* m_awaiter;

public:
    suspend_always initial_suspend() const noexcept { return suspend_always{}; }
    
    final_suspend_transfer final_suspend() noexcept
    {
        auto continuation = m_awaiter->m_continuation;

        return final_suspend_transfer
        {
            continuation
        };
    }
    
    future_type get_return_object()
    {
        return future_type{ static_cast<promise_type*>(this) };
    }

    void unhandled_exception() noexcept
    {
        m_awaiter->m_result.emplace<basic_task_awaiter_type::exception_index>(
            std::current_exception()
            );
    }
};

template<
    TaskTraits Traits
>
class basic_task_promise
    :
public basic_task_promise_base<Traits>
{
    template<
        TaskTraits Traits
    > friend class basic_task_awaiter;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;
    using basic_task_promise::basic_task_promise_base::m_awaiter;

    using basic_task_awaiter_type = typename basic_task_awaiter<Traits>;

public:
    template<
        typename TValue
    > void return_value(
        TValue&& result
    )
    {
        m_awaiter->m_result.emplace<basic_task_awaiter_type::value_index>(
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
    > friend class basic_task_awaiter;

    using basic_task_awaiter_type = typename basic_task_awaiter<Traits>;
    using basic_task_promise::basic_task_promise_base::m_awaiter;
public:
    void return_void()
    {
        m_awaiter->m_result.emplace<basic_task_awaiter_type::value_index>(std::monostate{});
    }
};

template<
    TaskTraits Traits
> class basic_task
    :
private noncopyable
{
    template<
        TaskTraits Traits
    > friend class basic_task_promise;

    template<
        TaskTraits Traits
    > friend class basic_task_awaiter;

public:
    using promise_type = typename Traits::promise_type;
    using awaiter_type = typename Traits::awaiter_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

protected:

    promise_type* m_promise;

    basic_task(
        promise_type* promise
    ) : m_promise(
        promise
    )
    {
    }

    basic_task(
        basic_task&& other
    ) : m_promise{ other.m_promise }
    {
        other.m_promise = nullptr;
    }

public:
    ~basic_task()
    {
        if (m_promise)
        {
            coroutine_handle<promise_type>::from_promise(*m_promise).destroy();
        }
    }

    awaiter_type operator co_await() &&
    {
        return awaiter_type 
        { 
            static_cast<future_type*>(this) 
        };
    }
};

// task and task_promise are the library-provided derivations
// of basic_task and basic_task_promise that add no behavior.
template<
    typename TResult = void
> class task;

template<
    typename TResult = void
> class task_promise;

template<
    typename TResult = void
> class task_awaiter;

template<
    typename TResult
> struct task_traits
{
    typedef task_promise<TResult> promise_type;
    typedef task<TResult> future_type;
    typedef TResult result_type;
    typedef task_awaiter<TResult> awaiter_type;
};

template<
    typename TResult
>
class task
    :
public basic_task<task_traits<TResult>>
{
    template <
        TaskTraits Traits
    > friend class basic_task_promise;

public:
    task(task_promise<TResult>* promise) 
        : task::basic_task(promise)
    {}
};

template<
    typename TResult
> class task_promise
    :
public basic_task_promise<task_traits<TResult>>
{
};

template<
    typename TResult
> class task_awaiter
    :
public basic_task_awaiter<task_traits<TResult>>
{
    template <
        TaskTraits Traits
    > friend class basic_task;

    using task_awaiter::basic_task_awaiter::basic_task_awaiter;
};

}
using detail::basic_task;
using detail::basic_task_promise;
using detail::task;
using detail::task_promise;
using detail::TaskTraits;
using detail::VoidTaskTraits;
using detail::ReferenceTaskTraits;

}