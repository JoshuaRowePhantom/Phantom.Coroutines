#ifndef PHANTOM_COROUTINES_INCLUDE_SHARED_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_SHARED_TASK_H
// shared_task and shared_task_promise implement a reference-counted task
// that can be co_await'ed multiple times.
// A shared_task<> itself can be copied or moved. 
// When a shared_task<> completes, the result of the await operation
// is a reference to the return value of the task.
// If the shared_task<>'s reference count reaches zero,
// the task is destroyed: this will likely lead to undefined behavior
// if the task is still executing, so don't do this.
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <atomic>
#include <optional>
#include <tuple>
#include <utility>
#include <variant>
#include "detail/atomic_state.h"
#include "detail/final_suspend_transfer.h"
#include "detail/variant_result_storage.h"
#include "extensible_promise.h"
#include "policies.h"
#include "type_traits.h"
#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class basic_shared_task;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    is_continuation Continuation
> class basic_shared_task_promise;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Policy
> concept is_shared_task_promise_policy =
is_continuation_type_policy<Policy>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    is_shared_task_promise_policy ... Policies
>
using shared_task_promise = basic_shared_task_promise<
    Result,
    select_continuation_type<
        Policies...,
        continuation_type<coroutine_handle<>>>
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result = void,
    is_shared_task_promise_policy ... Policies
>
using shared_task = basic_shared_task<shared_task_promise<Result, Policies...>>;

struct shared_task_states
{
    struct Completed {};
    struct Running {};
};

template<
    is_continuation Continuation
> struct shared_task_awaiter_list_entry
{
    shared_task_awaiter_list_entry* m_nextAwaiter = nullptr;
    Continuation m_continuation;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class shared_task_awaiter;

template<
    typename Promise
> class basic_shared_task
    :
    public extensible_promise_handle<Promise>
{
    using typename basic_shared_task::extensible_promise_handle::coroutine_handle_type;

    template<
        typename Result,
        is_continuation Continuation
    > friend class basic_shared_task_promise;

protected:
    basic_shared_task(
        coroutine_handle<Promise> handle
    ) noexcept 
        : basic_shared_task::extensible_promise_handle(handle)
    {}

    void acquire_reference() noexcept
    {
        if (*this)
        {
            this->promise().acquire_reference();
        }
    }

    void release_reference() noexcept
    {
        if (*this)
        {
            this->promise().release_reference();
        }
    }

public:
    typedef Promise promise_type;

    basic_shared_task()
        : basic_shared_task::extensible_promise_handle(nullptr)
    {}

    basic_shared_task(
        const basic_shared_task& other
    )  noexcept 
        : basic_shared_task::extensible_promise_handle(other)
    {
        acquire_reference();
    }

    ~basic_shared_task() noexcept
    {
        release_reference();
    }

    basic_shared_task(
        basic_shared_task&& other
    )  noexcept 
        : basic_shared_task::extensible_promise_handle(other)
    {
        other.handle() = nullptr;
    }

    auto& operator=(const basic_shared_task& other) noexcept
    {
        if (*this != other)
        {
            release_reference();
            this->handle() = other.handle();
            acquire_reference();
        }

        return *this;
    }

    basic_shared_task& operator=(
        basic_shared_task&& other
        ) noexcept
    {
        if (*this != other)
        {
            release_reference();
            this->handle() = other.handle();
            other.handle() = nullptr;
        }

        return *this;
    }

    auto operator co_await(
        this auto&& self
        ) noexcept
    {
        return shared_task_awaiter{ self.handle() };
    }

    auto when_ready(
        this auto&& self
    ) noexcept
    {
        struct awaiter : shared_task_awaiter<Promise>
        {
            using awaiter::shared_task_awaiter::shared_task_awaiter;

            void await_resume() const noexcept
            {
            }
        };

        return awaiter{ self.handle() };
    }

    bool is_ready(
        this auto& self
    ) noexcept
    {
        return self.handle() && self.promise().m_state.load(std::memory_order_acquire) == shared_task_states::Completed{};
    }
};

template<
    typename Promise
> class shared_task_awaiter
    :
    public extensible_promise_handle<Promise>,
    private shared_task_awaiter_list_entry<typename Promise::continuation_type>
{
    template<
        typename Result,
        is_continuation Continuation
    > friend class basic_shared_task_promise;

    template<
        typename
    > friend struct shared_task_promise_final_suspend_awaiter;

    using typename shared_task_awaiter::extensible_promise_handle::coroutine_handle_type;
    using continuation_type = typename Promise::continuation_type;

public:
    shared_task_awaiter(
        coroutine_handle_type handle
    ) noexcept : shared_task_awaiter::extensible_promise_handle(handle)
    {}

    bool await_ready(
        this auto& self
    ) noexcept
    {
        return self.promise().await_ready(
            self);
    }

    coroutine_handle<> await_suspend(
        this auto& self,
        continuation_type continuation
    ) noexcept
    {
        self.m_continuation = continuation;
        
        return self.promise().await_suspend(
            self,
            continuation);
    }

    decltype(auto) await_resume(
        this auto&& self
    )
    {
        return self.promise().await_resume(
            self);
    }
};

template<
    typename Promise
> shared_task_awaiter(coroutine_handle<Promise>) -> shared_task_awaiter<Promise>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> struct shared_task_promise_final_suspend_awaiter
    :
    public extensible_promise_handle<Promise>,
    private shared_task_states
{
    using extensible_promise_handle<Promise>::extensible_promise_handle;

    bool await_ready(
    ) const noexcept
    {
        return false;
    }

    coroutine_handle<> await_suspend(
        this auto& self,
        coroutine_handle<>
    ) noexcept
    {
        // Any thread reading the state and continuing execution will -acquire- m_state
        // to guarantee it can see the completed return value.  Therefore,
        // we -release- m_state.
        // 
        // This thread needs to -acquire- all the data written by other threads
        // when they updated the state to include awaiters into the linked list.
        // Therefore, we -acquire- m_state.
        auto previousState = self.promise().m_state.exchange(
            Completed{},
            std::memory_order_acq_rel
        );

        // In-line resume each awaiter except the last,
        // which we will resume via symmetric transfer.
        // Remember that we have to capture the next pointer
        // before resuming, because resuming will destroy the awaiter.
        // Note that there will always be at least one awaiter,
        // otherwise the promise would not have been started.
        auto awaiter = previousState.template as<Running>();
        while (true)
        {
            auto nextAwaiter = awaiter->m_nextAwaiter;
            if (!nextAwaiter)
            {
                // This waiter should be resumed via symmetric transfer.
                return awaiter->m_continuation;
            }

            // Otherwise the awaiter should be resume()'d
            awaiter->m_continuation.resume();
            awaiter = nextAwaiter;
        }
    }

    [[noreturn]]
    void await_resume(
    ) const noexcept
    {
        std::unreachable();
    }
};

template<
    typename Promise
> shared_task_promise_final_suspend_awaiter(coroutine_handle<Promise>) -> shared_task_promise_final_suspend_awaiter<Promise>;

template<
    typename Promise
> shared_task_promise_final_suspend_awaiter(Promise&) -> shared_task_promise_final_suspend_awaiter<Promise>;

template<
    typename Result,
    is_continuation Continuation
> class basic_shared_task_promise
    :
    public extensible_promise,
    protected detail::variant_result_storage<Result>,
    private shared_task_states,
    public detail::variant_return_result<Result>
{
    template<
        typename Promise
    > friend class shared_task_awaiter;

    template<
        typename Promise
    > friend struct shared_task_promise_final_suspend_awaiter;
    
public:
    typedef Continuation continuation_type;

private:
    friend class basic_shared_task<basic_shared_task_promise>;
    using awaiter_list_entry = shared_task_awaiter_list_entry<Continuation>;

    typedef atomic_state<
        SingletonState<Completed>,
        StateSet<Running, awaiter_list_entry*>
    > atomic_state_type;
    using state_type = typename atomic_state_type::state_type;
    static inline const auto NotStarted = state_type{ nullptr };

    atomic_state_type m_state;

    using typename basic_shared_task_promise::variant_result_storage::result_variant_member_type;
    using variant_type = std::variant<
        std::monostate,
        result_variant_member_type,
        std::exception_ptr
    >;

    variant_type m_resultVariant;
    static constexpr size_t ResultIndex = 1;
    static constexpr size_t ExceptionIndex = 2;

    // We start with a reference count of 1: 
    // one for the initial reference count of the
    // shared_task returned by get_return_object.
    std::atomic<size_t> m_referenceCount = 1;

    void acquire_reference(
        this auto& self
    ) noexcept
    {
        // Acquiring a reference needs no special memory ordering, just atomicity.
        self.m_referenceCount.fetch_add(1, std::memory_order_relaxed);
    }

    void release_reference(
        this auto& self
    ) noexcept
    {
        // The thread doing the releasing may have written to memory referenced by
        // the return value of the promise, so to ensure the thread
        // doing the releasing can destroy that memory, the fetch_sub
        // must -release- the reference count.

        // The last decrement will destroy the promise, so it will need to -acquire-
        // the reference count in order to guarantee it can read data written by
        // other thread, this data needing to be destroyed.
        auto previousReferenceCount = self.m_referenceCount.fetch_sub(1, std::memory_order_acq_rel);
        if (previousReferenceCount == 1)
        {
            self.handle().destroy();
        }
    }

    bool await_ready(
        this auto& self,
        auto& awaiter
    ) noexcept
    {
        std::ignore = awaiter;
        // If the task is complete, we need to make sure we can
        // read all the results of the task.
        // final_suspend_awaiter -released- m_state,
        // so we -acquire- it here.
        return self.m_state.load(std::memory_order_acquire)
            == Completed{};
    }

    coroutine_handle<> await_suspend(
        this auto& self,
        auto& awaiter,
        continuation_type continuation
    ) noexcept
    {
        auto previousState = compare_exchange_weak_loop(
            self.m_state,
            [&awaiter](auto state) -> std::optional<state_type>
            {
                if (state.template is<Completed>())
                {
                    return {};
                }

                awaiter.m_nextAwaiter = state.template as<Running>();
                return static_cast<awaiter_list_entry*>(&awaiter);
            },
            // We don't need strong memory order to initially load the value
            // for use in the lambda.
            std::memory_order_relaxed,
            // In the case that we start the shared_task, we need to -acquire-
            // the state left behind by the thread that created the promise.
            // -Probably- the shared_task was passed to another thread via an acquire / release operation,
            // but it's always possible that e.g. a caller wrote a shared_task* to a shared data structure
            // with relaxed semantics and it was cheaply acquired.
            // We also need to write with release semantics because the m_nextAwaiter must be readable
            // by whichever thread completes the task and dispatches the awaiters.
            std::memory_order_acq_rel,
            // We don't need special ordering rules for failure.
            std::memory_order_relaxed);

        if (previousState == Completed{})
        {
            return continuation;
        }

        if (previousState == NotStarted)
        {
            return self.handle();
        }

        return noop_coroutine();
    }

    decltype(auto) await_resume(
        this auto& self,
        auto& /* awaiter */)
    {
        if (self.m_resultVariant.index() == ExceptionIndex)
        {
            std::rethrow_exception(
                get<ExceptionIndex>(self.m_resultVariant));
        }

        return self.basic_shared_task_promise::variant_result_storage::template get_result<ResultIndex>(
            self.m_resultVariant);
    }

public:
    basic_shared_task_promise()
        : m_state{ NotStarted }
    {
        m_state.store(
            NotStarted,
            // Ensure that all the data needed for a thread that resumes
            // this shared_task_promise is visible.
            std::memory_order_release);
    }

    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return shared_task<Result>{ self.handle() };
    }

    auto initial_suspend(
    ) const noexcept
    {
        return suspend_always{};
    }

    auto final_suspend(
        this auto& self
    ) noexcept
    {
        return shared_task_promise_final_suspend_awaiter{ self };
    }

    void unhandled_exception(
        this auto& self
    ) noexcept
    {
        self.m_resultVariant.template emplace<ExceptionIndex>(
            std::current_exception());
    }

    void return_variant_result(
        this auto& self,
        auto&& result
    ) noexcept(noexcept(
        self.m_resultVariant.template emplace<ResultIndex>(
            std::forward<decltype(result)>(result))))
    {
        self.m_resultVariant.template emplace<ResultIndex>(
            std::forward<decltype(result)>(result));
    }
};
}
#endif
