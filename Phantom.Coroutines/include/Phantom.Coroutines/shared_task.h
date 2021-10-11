#include <variant>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"


namespace Phantom::Coroutines
{

namespace detail
{

template<
    typename TResult
> class shared_task;

}
}

namespace std
{
template<
    typename TResult,
    typename... Args
> struct coroutine_traits<
    Phantom::Coroutines::detail::shared_task<TResult>,
    Args...
>;
}

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TResult
> class shared_task;

template<
    typename TResult
> class shared_task_awaiter
{
    template<
        typename TResult
    > friend class shared_task_promise_base;

    template<
        typename TResult
    > friend class shared_task_promise;

    using shared_task_promise = shared_task_promise<TResult>;

    shared_task_awaiter* m_nextAwaiter;
    coroutine_handle<> m_continuation;
    shared_task_promise* m_promise;

    shared_task_awaiter(
        shared_task_promise* promise
    ) :
        m_promise
    {
        promise
    }
    {}

public:
    bool await_ready()
    {
        return m_promise->await_ready();
    }

    auto await_suspend(
        coroutine_handle<> continuation)
    {
        return m_promise->await_suspend(
            this,
            continuation);
    }

    auto await_resume()
    {
        return (m_promise->await_resume(
            this));
    }
};

template<
    typename Traits
>
class shared_task_promise;

template<
    typename Traits
>
class shared_task_promise_base
{
public:
    typedef Traits traits_type;
    typedef typename traits_type::future_type future_type;
    typedef typename future_type::result_type result_type;
    typedef typename traits_type::promise_type promise_type;

private:

    template<
        typename Traits
    > friend class shared_task_base;

    template<
        typename Traits
    > friend class shared_task_promise;

    template<
        typename TResult
    > friend class shared_task_awaiter;

    using shared_task_awaiter = shared_task_awaiter<result_type>;

    struct CompletedState {};
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<CompletedState>,
        StateSet<WaitingCoroutineState, shared_task_awaiter*>
    > atomic_state_type;
    typedef atomic_state_type::state_type state_type;

    static const inline state_type NotStartedState = state_type{ nullptr };
    atomic_state_type m_atomicState = NotStartedState;

    // Reference count starts at 2 to avoid two atomic increment operations.
    // 1 for the running coroutine,
    // 1 for the first shared_task object.
    std::atomic<size_t> m_referenceCount = 2;

    static constexpr bool is_void = std::same_as<void, result_type>;

    typedef std::conditional_t<
        is_void,
        std::monostate,
        result_type
    > result_storage_type;

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
        result_storage_type,
        std::exception_ptr
    > result_variant_type;

    const size_t return_value_index = 1;
    const size_t unhandled_exception_index = 2;

    result_variant_type m_result;

    ~shared_task_promise_base()
    {
#ifndef NDEBUG
        auto state = m_atomicState.load(std::memory_order_acquire);

        assert(
            state == CompletedState{}
        );
#endif
    }

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
        shared_task_awaiter* awaiter,
        coroutine_handle<> continuation
    )
    {
        auto previousState = compare_exchange_weak_loop(
            m_atomicState,
            [=](state_type previousState) -> std::optional<state_type>
        {
            if (is_ready(previousState))
            {
                return std::nullopt;
            }

            awaiter.m_nextAwaiter = previousState.as<WaitingCoroutineState>();
            return state_type{ awaiter };
        }
        );

        // The first awaiter triggers the coroutine to start execution.
        if (previousState == NotStartedState)
        {
            return get_coroutine_handle();
        }

        if (is_ready(previousState))
        {
            return continuation;
        }

        awaiter->m_continuation = continuation;

        return noop_coroutine();
    }

    auto& await_resume()
    {
        if (m_result.index() == unhandled_exception_index)
        {
            std::rethrow_exception(
                m_result.get<unhandled_exception_index>()
            );
        }

        return m_result.get<return_value_index>();
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
        return future_type{ this };
    }

    final_suspend_transfer final_suspend()
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
    typename Traits
> class shared_task_promise
    :
    public shared_task_promise_base<Traits>
{
public:
    using shared_task_promise::shared_task_promise_base::shared_task_promise_base;

    template<
        typename TReturnValue
    >
        void return_value(
            TReturnValue&& value
        )
    {
        set_result(
            std::forward<TReturnValue>(value)
        );
    }
};

template<
    typename Traits
> requires
std::same_as<void, typename Traits::result_type>
class shared_task_promise<
    Traits
>
    :
    public shared_task_promise_base<Traits>
{
public:
    using shared_task_promise::shared_task_promise_base::shared_task_promise_base;

    void return_void()
    {
        shared_task_promise::shared_task_promise_base::set_result(
            std::monostate{}
        );
    }
};

template<
    typename Traits
> class shared_task_base
{
public:
    using promise_type = Traits::promise_type;
    using future_type = Traits::future_type;
    using result_type = Traits::result_type;

private:
    promise_type* m_promise;

    shared_task_base(
        promise_type* promise
    ) :
        m_promise{ promise }
    {
        // Do not acquire here.
        // The promise is constructed with a reference count that
        // includes the first shared_task's reference.
    }

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

protected:

    shared_task_base(
        const shared_task_base& other
    ) :
        m_promise{ other.m_promise }
    {
        acquire_reference();
    }

    shared_task_base(
        shared_task_base&& other
    ) :
        m_promise{ other.m_promise }
    {
        other.m_promise = nullptr;
    }

    shared_task_base& operator = (
        const shared_task_base& other
        )
    {
        release_reference();
        m_promise = other.m_promise;
        acquire_reference();
        return *this;
    }

    shared_task_base& operator = (
        shared_task_base&& other
        )
    {
        release_reference();
        m_promise = other.m_promise;
        other.m_promise = nullptr;
        return *this;
    }

    ~shared_task_base()
    {
        release_reference();
    }

    shared_task_base()
        : m_promise{ nullptr }
    {}

public:
    shared_task_awaiter<result_type> operator co_await()
    {
        return shared_task_awaiter{ m_promise };
    }
};

template<
    typename TResult
>
struct shared_task_traits
{
    typedef shared_task_promise<shared_task_traits> promise_type;
    typedef shared_task<TResult> future_type;
    typedef TResult result_type;
};

template <
    typename TResult
> class shared_task :
    public shared_task_base<
        shared_task_traits<TResult>
    >
{
public:
    using traits_type = shared_task_traits<TResult>;
    using promise_type = typename traits_type::promise_type;
    using shared_task::shared_task_base::shared_task_base;
};

}
using detail::shared_task;
}