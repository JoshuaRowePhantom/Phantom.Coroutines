#pragma once

#include <variant>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/variant_result_storage.h"

namespace Phantom::Coroutines
{

namespace detail
{

// The Traits parameter to basic_shared_task, basic_shared_task_promise must satisfy this concept.
template<
    typename Traits
> concept SharedTaskTraits = requires
{
    // The basic_task_promise-derived class that implements the promise type.
    typename Traits::promise_type;

    // The basic_task-derived class that implements the future type.
    typename Traits::future_type;

    // The result type of the task.
    typename Traits::result_type;

    // The awaiter type,
    // which must be a template accepting the future_type or future_type&.
    typename Traits::template awaiter_type<typename Traits::future_type>;
    typename Traits::template awaiter_type<typename Traits::future_type&>;
};

// A specialization of SharedTaskTraits to detect void-returning tasks.
template<
    typename Traits
> concept VoidSharedTaskTraits =
SharedTaskTraits<Traits>
&&
std::same_as<void, typename Traits::result_type>;

// A specialization of SharedTaskTraits to detect reference-returning tasks.
template<
    typename Traits
> concept ReferenceSharedTaskTraits =
SharedTaskTraits<Traits>
&&
std::is_reference_v<typename Traits::result_type>;

template<
    SharedTaskTraits Traits
>
class basic_shared_task_promise;

class shared_task_awaiter_list_entry
{
    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task_promise_base;

    shared_task_awaiter_list_entry* m_nextAwaiter;
    coroutine_handle<> m_continuation;
};

template<
    SharedTaskTraits Traits,
    typename FutureType
> class basic_shared_task_awaiter
    :
    private shared_task_awaiter_list_entry,
    private immovable_object
{
    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task_promise_base;

    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task_promise;

    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task;

    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

    FutureType m_future;

    promise_type* promise()
    {
        return m_future.m_promise;
    }

protected:
    basic_shared_task_awaiter(
        FutureType&& future
    ) :
        m_future
    {
        std::forward<FutureType>(future)
    }
    {}

public:
    bool await_ready()
    {
        return promise()->await_ready();
    }

    auto await_suspend(
        coroutine_handle<> continuation)
    {
        return promise()->await_suspend(
            this,
            continuation);
    }

    decltype(auto) await_resume()
    {
        if constexpr (
            std::is_reference_v<FutureType>
            ||
            std::is_reference_v<result_type>
            ||
            std::is_void_v<result_type>)
        {
            return (promise()->await_resume());
        }
        else
        {
            return (std::move(promise()->await_resume()));
        }
    }
};

template<
    SharedTaskTraits Traits
>
class basic_shared_task_promise;

template<
    SharedTaskTraits Traits
>
class basic_shared_task_promise_base
    :
private variant_result_storage<
    typename Traits::result_type
>
{
public:
    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

private:

    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task;

    template<
        SharedTaskTraits Traits
    > friend class basic_shared_task_promise;

    template<
        SharedTaskTraits Traits,
        typename FutureType
    > friend class basic_shared_task_awaiter;

    struct CompletedState {};
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<CompletedState>,
        StateSet<WaitingCoroutineState, shared_task_awaiter_list_entry*>
    > atomic_state_type;
    typedef atomic_state_type::state_type state_type;

    static const inline state_type NotStartedState = state_type{ nullptr };
    atomic_state_type m_atomicState = NotStartedState;

    // Reference count starts at 1 to avoid an atomic increment operation
    std::atomic<size_t> m_referenceCount = 1;

    using typename basic_shared_task_promise_base::variant_result_storage::result_variant_member_type;
    using basic_shared_task_promise_base::variant_result_storage::is_void;
    using basic_shared_task_promise_base::variant_result_storage::is_reference;
    using basic_shared_task_promise_base::variant_result_storage::is_rvalue_reference;

    static_assert(!is_rvalue_reference);

    // While we -could- use extra states in m_atomicState to store
    // the result object state, this has some disadvantages.
    // In order to implement symmetric transfer in final_suspend,
    // we would have to have storage for another variable for the coroutine_handle
    // to continue, or we would need to perform multiple operations on the
    // atomic state object to set its state to the result type while preserving
    // the chain of awaiters and then again set its state to completed.
    // Since we need extra space anyway, we leave
    // m_atomicState to store the linked list of continuations or
    // the terminal state, and store the terminal state's value
    // in a variant.
    typedef std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    > result_variant_type;

    static const size_t return_value_index = 1;
    static const size_t unhandled_exception_index = 2;

    result_variant_type m_result;

    promise_type& get_promise() { return static_cast<promise_type&>(*this); }
    auto get_coroutine_handle() { return coroutine_handle<promise_type>::from_promise(get_promise()); }

    void increment_reference_count()
    {
        m_referenceCount.fetch_add(1, std::memory_order_relaxed);
    }

    void decrement_reference_count()
    {
        if (1 != m_referenceCount.fetch_sub(1, std::memory_order_acq_rel))
        {
            return;
        }

        get_coroutine_handle().destroy();
    }

    bool is_ready(
        state_type state)
    {
        return state == CompletedState{};
    }

    bool await_ready()
    {
        return is_ready(m_atomicState.load(std::memory_order_acquire));
    }

    coroutine_handle<> await_suspend(
        shared_task_awaiter_list_entry* awaiter,
        coroutine_handle<> continuation
    )
    {
        awaiter->m_continuation = continuation;
        
        auto previousState = compare_exchange_weak_loop(
            m_atomicState,
            [=](state_type previousState) -> std::optional<state_type>
        {
            if (is_ready(previousState))
            {
                return std::nullopt;
            }

            awaiter->m_nextAwaiter = previousState.as<WaitingCoroutineState>();
            return state_type{ awaiter };
        }
        );

        // The first awaiter triggers the coroutine to start execution.
        if (previousState == NotStartedState)
        {
            return get_coroutine_handle();
        }

        // If the task is already ready, just continue.
        if (is_ready(previousState))
        {
            return continuation;
        }

        // Otherwise, there is a "join" operation here;
        // this is not the first co_await on the shared_task, so
        // there's nothing to start,
        // but the task is not complete so there's nothing to resume.
        return noop_coroutine();
    }

    decltype(auto) await_resume()
    {
        if (m_result.index() == unhandled_exception_index)
        {
            std::rethrow_exception(
                get<unhandled_exception_index>(m_result)
            );
        }

        if constexpr (is_void)
        {
            return;
        }
        else if constexpr (is_rvalue_reference)
        {
            return std::move(get<return_value_index>(m_result).get());
        }
        else if constexpr (is_reference)
        {
            return get<return_value_index>(m_result).get();
        }
        else
        {
            return (get<return_value_index>(m_result));
        }
    }

    template<
        typename TReturnValue
    > void set_result(
        TReturnValue&& returnValue
    )
    {
        m_result.emplace<return_value_index>(
            std::forward<TReturnValue>(returnValue)
            );
    }

public:
    suspend_always initial_suspend() const { return {}; }

    future_type get_return_object()
    {
        return future_type{ &get_promise() };
    }

    final_suspend_transfer final_suspend() noexcept
    {
        auto state = m_atomicState.exchange(
            CompletedState{},
            std::memory_order_acq_rel
        );

        // This will be non-null, because we required there to be at
        // least one awaiter to start the shared_task.
        auto awaiter = state.as<WaitingCoroutineState>();

        // For every awaiter except the last, resume those awaiters.
        while (awaiter->m_nextAwaiter)
        {
            auto nextAwaiter = awaiter->m_nextAwaiter;
            awaiter->m_continuation.resume();
            awaiter = nextAwaiter;
        }

        // For the last awaiter (which would've been the first that
        // co_await'ed the shared_task), use symmetric transfer
        // to resume it.
        return { awaiter->m_continuation };
    }

    void unhandled_exception()
    {
        m_result.emplace<unhandled_exception_index>(
            std::current_exception());
    }
};

template<
    SharedTaskTraits Traits
> class basic_shared_task_promise
    :
public basic_shared_task_promise_base<Traits>
{
public:
    using basic_shared_task_promise::basic_shared_task_promise_base::basic_shared_task_promise_base;

    template<
        typename TReturnValue
    >
        void return_value(
            TReturnValue&& value
        )
    {
        basic_shared_task_promise::basic_shared_task_promise_base::set_result(
            std::forward<TReturnValue>(value)
        );
    }
};

template<
    VoidSharedTaskTraits Traits
> 
class basic_shared_task_promise<
    Traits
>
    :
public basic_shared_task_promise_base<
    Traits
>
{
public:
    using basic_shared_task_promise::basic_shared_task_promise_base::basic_shared_task_promise_base;

    void return_void()
    {
        basic_shared_task_promise::basic_shared_task_promise_base::set_result(
            std::monostate{}
        );
    }
};

template<
    SharedTaskTraits Traits
> class basic_shared_task
{
    template<
        SharedTaskTraits Traits,
        typename FutureType
    > friend class basic_shared_task_awaiter;

public:
    using promise_type = typename Traits::promise_type;
    using future_type = typename Traits::future_type;
    using result_type = typename Traits::result_type;

private:
    promise_type* m_promise;

    void release_reference()
    {
        if (m_promise)
        {
            m_promise->decrement_reference_count();
        }
    }

    void acquire_reference()
    {
        if (m_promise)
        {
            m_promise->increment_reference_count();
        }
    }

public:

    basic_shared_task(
        promise_type* promise
    ) :
        m_promise{ promise }
    {
        // Do not acquire here.
        // The promise is constructed with a reference count that
        // includes the first shared_task's reference.
    }

    basic_shared_task(
        const basic_shared_task& other
    ) :
        m_promise{ other.m_promise }
    {
        acquire_reference();
    }

    basic_shared_task(
        basic_shared_task&& other
    ) :
        m_promise{ other.m_promise }
    {
        other.m_promise = nullptr;
    }

    basic_shared_task& operator = (
        const basic_shared_task& other
        )
    {
        release_reference();
        m_promise = other.m_promise;
        acquire_reference();
        return *this;
    }

    basic_shared_task& operator = (
        basic_shared_task&& other
        )
    {
        release_reference();
        m_promise = other.m_promise;
        other.m_promise = nullptr;
        return *this;
    }

    ~basic_shared_task()
    {
        release_reference();
    }

    basic_shared_task()
        : m_promise{ nullptr }
    {}

    auto operator co_await() &
    {
        return typename Traits::template awaiter_type<future_type&>{ static_cast<future_type&>(*this) };
    }

    auto operator co_await() &&
    {
        return typename Traits::template awaiter_type<future_type>{ static_cast<future_type&&>(*this) };
    }
};

template<
    typename TResult
> class shared_task_promise;

template<
    typename TResult = void
> class shared_task;

template<
    typename FutureType
> class shared_task_awaiter;

template<
    typename TResult
>
struct shared_task_traits
{
    typedef shared_task_promise<TResult> promise_type;
    typedef shared_task<TResult> future_type;
    typedef TResult result_type;
    template<
        typename FutureType
    >
    using awaiter_type = shared_task_awaiter<FutureType>;
};

template <
    typename TResult
> class shared_task_promise :
    public basic_shared_task_promise<
        shared_task_traits<TResult>
    >
{
public:
    using shared_task_promise::basic_shared_task_promise::basic_shared_task_promise;
};

template <
    typename TResult
> class shared_task :
    public basic_shared_task<
        shared_task_traits<TResult>
    >
{
public:
    using shared_task::basic_shared_task::basic_shared_task;
};

template<
    typename TResult
> class shared_task_awaiter<
    shared_task<TResult>
>
    :
public basic_shared_task_awaiter<
    shared_task_traits<TResult>,
    shared_task<TResult>
>
{
public:
    using shared_task_awaiter::basic_shared_task_awaiter::basic_shared_task_awaiter;
};

template<
    typename TResult
> class shared_task_awaiter<
    shared_task<TResult>&
>
    :
public basic_shared_task_awaiter<
    shared_task_traits<TResult>,
    shared_task<TResult>&
>
{
public:
    using shared_task_awaiter::basic_shared_task_awaiter::basic_shared_task_awaiter;
};

}
using detail::shared_task;
}