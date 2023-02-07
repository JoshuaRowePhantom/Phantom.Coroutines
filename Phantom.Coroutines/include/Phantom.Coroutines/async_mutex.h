#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "awaiter_list.h"
#include <type_traits>

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
    is_ordering_policy OrderingPolicy
>
class basic_async_mutex;

template<
    typename T
> concept is_async_mutex_policy =
is_concrete_policy<T, await_is_not_cancellable>
|| is_await_result_on_destruction_policy<T>
// It might appear that allowing only a single awaiter for a mutex
// wouldn't be useful, but actually it is:
// a common case is that there only two threads of control vying
// for the mutex, and therefore only one of them can be awaiting.
|| is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>
|| is_ordering_policy<T>;

template<
    is_async_mutex_policy ... Policy
> using async_mutex = basic_async_mutex<
    select_await_cancellation_policy<Policy..., await_is_not_cancellable>,
    select_continuation_type<Policy..., default_continuation_type>,
    select_awaiter_cardinality_policy<Policy..., multiple_awaiters>,
    select_await_result_on_destruction_policy<Policy..., noop_on_destroy>,
    select_ordering_policy<Policy..., fifo_ordering>
>;

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_awaiter_cardinality_policy AwaiterCardinalityPolicy,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
    is_ordering_policy OrderingPolicy
>
class basic_async_mutex
    :
private immovable_object,
private awaiter_list_mutex<AwaitCancellationPolicy>
{
public:
    using lock_type = std::unique_lock<basic_async_mutex>;

private:
    struct UnlockedState {};
    struct DestroyedState {};
    struct LockedState;

public:
    class [[nodiscard]] lock_operation
        :
        private immovable_object,
        public awaiter_list_entry<AwaiterCardinalityPolicy, lock_operation>
    {
        friend class basic_async_mutex;

        basic_async_mutex* m_mutex;

        Continuation m_continuation;

        lock_operation(
            basic_async_mutex* mutex
        ) :
            m_mutex(mutex)
        {}

    public:
        bool await_ready() const noexcept { return false; }

        bool await_suspend(
            Continuation continuation
        ) noexcept
        {
            m_continuation = continuation;

            auto nextStateLambda = [&](
                state_type previousState
                ) -> state_type
            {
                if (previousState == UnlockedState{})
                {
                    return LockedNoWaitersState;
                }

                this->set_next(previousState.as<LockedState>());
                return this;
            };

            auto previousState = compare_exchange_weak_loop(
                m_mutex->m_state,
                nextStateLambda
            );

            return previousState != UnlockedState{};
        }

        void resume()
        {
            m_continuation.resume();
        }

        void resume_on_mutex_destruction()
        {
            m_mutex = nullptr;
            m_continuation.resume();
        }

        void await_resume() noexcept(noexcept(resume_from_destruction_of_awaitable_object(AwaitResultOnDestructionPolicy{})))
        {
            if (!m_mutex)
            {
                resume_from_destruction_of_awaitable_object(AwaitResultOnDestructionPolicy{});
            }
        }
    };

    class [[nodiscard]] scoped_lock_operation
        :
        private immovable_object
    {
        friend class basic_async_mutex;

        basic_async_mutex& m_mutex;
        lock_operation m_lockOperation;

        scoped_lock_operation(
            basic_async_mutex& mutex
        ) :
            m_mutex{mutex},
            m_lockOperation{&mutex}
        {}

    public:
        bool await_ready() const noexcept 
        { 
            return m_lockOperation.await_ready(); 
        }

        bool await_suspend(
            coroutine_handle<> continuation
        ) noexcept
        {
            return m_lockOperation.await_suspend(
                continuation);
        }

        [[nodiscard]] lock_type await_resume() noexcept
        {
            return lock_type { m_mutex, std::adopt_lock };
        }
    };

private:

    typedef atomic_state<
        SingletonState<UnlockedState>,
        SingletonState<DestroyedState>,
        StateSet<LockedState, lock_operation*>
    > atomic_state_type;
    typedef atomic_state_type::state_type state_type;

    static inline const state_type LockedNoWaitersState = nullptr;

    atomic_state_type m_state = UnlockedState{};
    lock_operation* m_awaiters = nullptr;

public:
    bool try_lock() noexcept
    {
        state_type expectedState = UnlockedState{};
        return m_state.compare_exchange_strong(
            expectedState,
            LockedNoWaitersState,
            std::memory_order_acquire
        );
    }

    [[nodiscard]] lock_type try_scoped_lock() noexcept
    {
        if (try_lock())
        {
            return lock_type{ *this, std::adopt_lock };
        }
        else
        {
            return lock_type{};
        }
    }

    // We name this method lock_async
    // so that std::unique_lock::lock cannot find it.
    lock_operation lock_async()  noexcept
    {
        return lock_operation{ this };
    }

    scoped_lock_operation scoped_lock_async() noexcept
    {
        return scoped_lock_operation{ *this };
    }

    void unlock() noexcept
    {
        // We desire to service awaiters in order that they requested awaiting.
        // This prevents starvation.
        // We maintain the ordered list in m_awaiters;
        // when that empties out, we copy the atomically added awaiters into
        // m_awaiters.
        if (!m_awaiters)
        {
            state_type previousState = m_state.load(std::memory_order_relaxed);
            state_type nextState = nullptr;
            lock_operation* awaiters;
            do
            {
                if (previousState.is<LockedState>())
                {
                    awaiters = previousState.as<LockedState>();
                }
                else
                {
                    awaiters = nullptr;
                }
                
                if (awaiters)
                {
                    nextState = LockedNoWaitersState;
                }
                else
                {
                    nextState = UnlockedState{};
                }
            } while (!m_state.compare_exchange_weak(
                previousState,
                nextState,
                std::memory_order_acq_rel
            ));

            reverse_and_prepend_awaiter_list(
                awaiters,
                &m_awaiters);
        }

        if (m_awaiters)
        {
            auto awaiter = m_awaiters;
            m_awaiters = m_awaiters->next();

            // This has the potential to overflow the stack.
            // We expect callers to be using suspend_result.
            awaiter->resume();
        }

        return;
    }

    ~basic_async_mutex()
        requires std::derived_from<AwaitResultOnDestructionPolicy, noop_on_destroy>
    = default;

    ~basic_async_mutex()
        requires !std::derived_from<AwaitResultOnDestructionPolicy, noop_on_destroy>
    {
        invoke_on_awaiters(
            m_awaiters,
            [](auto awaiter)
            {
                awaiter->resume_on_mutex_destruction();
            }
        );

        auto previousState = m_state.exchange(
            DestroyedState{},
            std::memory_order_acquire);

        if (previousState.is<LockedState>())
        {
            invoke_on_awaiters(
                previousState.as<LockedState>(),
                [](auto awaiter)
                {
                    awaiter->resume_on_mutex_destruction();
                }
            );
        }
    }
};

}

using detail::async_mutex;
using detail::is_async_mutex_policy;

}
