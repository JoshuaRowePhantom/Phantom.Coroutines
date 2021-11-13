#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
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
>
class basic_task_promise_base
    :
private immovable_object
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
    
    final_suspend_transfer_and_destroy final_suspend() noexcept
    {
        return final_suspend_transfer_and_destroy
        {
            m_task->m_continuation
        };
    }
    
    future_type get_return_object()
    {
        return future_type{ static_cast<promise_type*>(this) };
    }

    void unhandled_exception() noexcept
    {
        m_task->m_result.emplace<basic_task<Traits>::exception_index>(
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
        TaskTraits Trait
    > friend class basic_task;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;
    using basic_task_type = basic_task<Traits>;
    using basic_task_promise::basic_task_promise_base::m_task;

public:
    template<
        typename TValue
    > void return_value(
        TValue&& result
    )
    {
        m_task->m_result.emplace<basic_task_type::value_index>(
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
    void return_void()
    {
        m_task->m_result.emplace<task<void>::value_index>(std::monostate{});
    }
};

template<
    TaskTraits Traits
> struct basic_task_result_type
{
    typedef Traits::result_type result_variant_member_type;
    static constexpr bool is_void = false;
    static constexpr bool is_reference = false;
};

template<
    VoidTaskTraits Traits
> struct basic_task_result_type<
    Traits
>
{
    typedef std::monostate result_variant_member_type;
    static constexpr bool is_void = true;
    static constexpr bool is_reference = false;
};

template<
    ReferenceTaskTraits Traits
> struct basic_task_result_type<
    Traits
>
{
    typedef std::reference_wrapper<std::remove_reference_t<typename Traits::result_type>> result_variant_member_type;
    static constexpr bool is_void = false;
    static constexpr bool is_reference = true;
};

template<
    TaskTraits Traits
> class basic_task
    :
private basic_task_result_type<Traits>,
private immovable_object
{
    using typename basic_task::basic_task_result_type::result_variant_member_type;
    using basic_task::basic_task_result_type::is_void;
    using basic_task::basic_task_result_type::is_reference;

    template<
        TaskTraits Traits
    > friend class basic_task_promise;

    template<
        TaskTraits Traits
    > friend class basic_task_promise_base;

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

    static const size_t value_index = 1;
    static const size_t exception_index = 2;

    result_variant_type m_result;

    // We only need the promise object until await_suspend
    // has been called; then we tell the promise object
    // about this object and set the continuation
    // member.
    union
    {
        promise_type* m_promise = nullptr;
        coroutine_handle<> m_continuation;
    };

    basic_task(
        promise_type* promise
    ) : m_promise(
        promise
    )
    {
        promise->m_task = static_cast<future_type*>(this);
    }

public:
    bool await_ready() const { return false; }

    coroutine_handle<> await_suspend(
        coroutine_handle<> continuation
    )
    {
        // Setting m_continuation below resets promise,
        // so save it here.
        auto promise = m_promise;
        m_continuation = continuation;
        return coroutine_handle<promise_type>::from_promise(*promise);
    }

    decltype(auto) await_resume()
    {
        if (m_result.index() == exception_index)
        {
            std::rethrow_exception(
                get<exception_index>(m_result));
        }

        if constexpr (is_void)
        {
            return;
        }
        else if constexpr (is_reference)
        {
            // If the result type is a reference type, unwrap the contained reference_wrapper.
            return (static_cast<result_type>(std::get<value_index>(m_result).get()));
        }
        else
        {
            return (static_cast<result_type&&>((std::get<value_index>(m_result))));
        }
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
    typename TResult
> struct task_traits
{
    typedef task_promise<TResult> promise_type;
    typedef task<TResult> future_type;
    typedef TResult result_type;
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
{
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