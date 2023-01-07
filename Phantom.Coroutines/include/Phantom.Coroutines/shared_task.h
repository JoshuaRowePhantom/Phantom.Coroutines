// shared_task and shared_task_promise implement a reference-counted task
// that can be co_await'ed multiple times.
// A shared_task<> itself can be copied or moved. 
// When a shared_task<> completes, the result of the await operation
// is a reference to the return value of the task.
// If the shared_task<>'s reference count reaches zero,
// the task is destroyed: this will likely lead to undefined behavior
// if the task is still executing, so don't do this.

#pragma once

#include <variant>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/variant_result_storage.h"
#include "extensible_promise.h"

namespace Phantom::Coroutines
{

struct shared_task_states
{
    struct Completed {};
    struct Running {};
};

template<
    typename Result,
    is_coroutine_handle Continuation = std::coroutine_handle<>
> class shared_task_promise;

template<
    typename Result = void,
    typename Promise = shared_task_promise<Result>
> class shared_task
    :
    public extensible_awaitable<Promise>
{
    using shared_task::extensible_awaitable::coroutine_handle_type;

    friend class shared_task_promise<Result, typename Promise::continuation_type>;
protected:
    shared_task(
        coroutine_handle<Promise> handle
    ) noexcept 
        : shared_task::extensible_awaitable(handle)
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

    shared_task()
        : shared_task::extensible_awaitable(nullptr)
    {}

    shared_task(
        const shared_task& other
    )  noexcept 
        : shared_task::extensible_awaitable(other)
    {
        acquire_reference();
    }

    ~shared_task() noexcept
    {
        release_reference();
    }

    shared_task(
        shared_task&& other
    )  noexcept 
        : shared_task::extensible_awaitable(other)
    {
        other.handle() = nullptr;
    }

    shared_task& operator=(const shared_task& other) noexcept
    {
        if (*this != other)
        {
            release_reference();
            this->handle() = other.handle();
            acquire_reference();
        }

        return *this;
    }

    shared_task& operator=(
        shared_task&& other
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
        return typename Promise::awaiter{ self.handle() };
    }
};

template<
    typename Result,
    is_coroutine_handle Continuation
> class shared_task_promise
    :
    public extensible_promise,
    protected detail::variant_result_storage<Result>,
    private shared_task_states,
    public detail::variant_return_result<Result>
{
public:
    typedef Continuation continuation_type;

private:
    friend class shared_task<Result, shared_task_promise>;

    struct final_suspend_awaiter
        :
        private shared_task_states
    {
        shared_task_promise& m_promise;

        final_suspend_awaiter(
            shared_task_promise& promise
        ) : m_promise{ promise }
        {}

        bool await_ready(
            this const auto& self
        ) noexcept
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
            auto previousState = self.m_promise.m_state.exchange(
                Completed{},
                std::memory_order_acq_rel
            );

            // In-line resume each awaiter except the last,
            // which we will resume via symmetric transfer.
            // Remember that we have to capture the next pointer
            // before resuming, because resuming will destroy the awaiter.
            // Note that there will always be at least one awaiter,
            // otherwise the promise would not have been started.
            auto awaiter = previousState.as<Running>();
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
            this auto& self
        ) noexcept
        {
            // This should never be called.
            assert(false);
        }
    };

    class awaiter
        :
        public extensible_awaitable<shared_task_promise>,
        private shared_task_states
    {
        friend class final_suspend_awaiter;
        using typename awaiter::extensible_awaitable::coroutine_handle_type;
        using continuation_type = Continuation;

        continuation_type m_continuation;
        awaiter* m_nextAwaiter = nullptr;

    public:
        awaiter(
            coroutine_handle_type handle
        ) noexcept : awaiter::extensible_awaitable(handle)
        {}

        bool await_ready(
            this auto& self
        ) noexcept
        {
            // If the task is complete, we need to make sure we can
            // read all the results of the task.
            // final_suspend_awaiter -released- m_state,
            // so we -acquire- it here.
            return self.promise().m_state.load(std::memory_order_acquire)
                == Completed{};
        }

        coroutine_handle<> await_suspend(
            this auto& self,
            continuation_type continuation
        ) noexcept
        {
            self.m_continuation = continuation;

            auto previousState = compare_exchange_weak_loop(
                self.promise().m_state,
                [&self](auto state) -> std::optional<state_type>
                {
                    if (state.is<Completed>())
                    {
                        return {};
                    }

                    self.m_nextAwaiter = state.as<Running>();
                    return &self;
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
            this auto& self
        )
        {
            return self.promise().await_resume();
        }
    };

    typedef atomic_state<
        SingletonState<Completed>,
        StateSet<Running, awaiter*>
    > atomic_state_type;
    using state_type = typename atomic_state_type::state_type;
    static inline const auto NotStarted = state_type{ nullptr };

    atomic_state_type m_state;

    using typename shared_task_promise::variant_result_storage::result_variant_member_type;
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

    decltype(auto) await_resume()
    {
        if (m_resultVariant.index() == ExceptionIndex)
        {
            rethrow_exception(
                get<ExceptionIndex>(m_resultVariant));
        }

        return shared_task_promise::variant_result_storage::get_result<ResultIndex>(
            m_resultVariant);
    }

public:
    shared_task_promise()
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
        this auto& self
    ) noexcept
    {
        return suspend_always{};
    }

    auto final_suspend(
        this auto& self
    ) noexcept
    {
        return final_suspend_awaiter{ self };
    }

    void unhandled_exception(
        this auto& self
    ) noexcept
    {
        self.m_resultVariant.emplace<ExceptionIndex>(
            std::current_exception());
    }

    void return_variant_result(
        this auto& self,
        auto&& result
    ) noexcept(noexcept(
        self.m_resultVariant.emplace<ResultIndex>(
            std::forward<decltype(result)>(result))))
    {
        self.m_resultVariant.emplace<ResultIndex>(
            std::forward<decltype(result)>(result));
    }
};
}