#ifndef PHANTOM_COROUTINES_INCLUDE_ASYNC_READER_WRITER_LOCK_H
#define PHANTOM_COROUTINES_INCLUDE_ASYNC_READER_WRITER_LOCK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/config.h"
#include "awaiter_list.h"
#include "double_wide_atomic.h"
#include "policies.h"
#include "tagged_pointer.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
    is_ordering_policy OrderingPolicy
>
class basic_async_reader_writer_lock;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> concept is_async_reader_writer_lock_policy =
is_concrete_policy<T, await_is_not_cancellable>
|| is_concrete_policy<T, noop_on_destroy>
|| is_concrete_policy<T, fail_on_destroy_with_awaiters>
// Cardinality policies aren't useful for reader / writer locks
// || is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>
|| is_concrete_policy<T, fifo_ordering>
|| is_concrete_policy<T, no_ordering_preference>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_async_reader_writer_lock_policy... Policies
> using async_reader_writer_lock = basic_async_reader_writer_lock<
    select_await_cancellation_policy<Policies..., await_is_not_cancellable>,
    select_continuation_type<Policies..., default_continuation_type>,
    select_await_result_on_destruction_policy<Policies..., noop_on_destroy>,
    select_ordering_policy<Policies..., fifo_ordering>
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
    is_ordering_policy WriterPreferencePolicy
>
class basic_async_reader_writer_lock
    :
    public immovable_object
{
public:
    class reader_lock;
    class writer_lock;

    using read_lock = std::unique_lock<reader_lock>;
    using write_lock = std::unique_lock<writer_lock>;

private:
    enum class operation_type
    {
        read,
        write
    };

    enum QueueState : uintptr_t
    {
        NotResuming_NoPending = 0,
        NotResuming_HasPending = 1,
        IsResuming_NoPending = 2,
        IsResuming_HasPending = 3,
        HasPendingMask = 1,
        IsResumingMask = 2,
    };

    struct alignas(16) operation_node
    { 
        operation_node* m_next;
        Continuation m_continuation;
        operation_type m_operationType;
    };

    class operation;

    struct state
    {
        tagged_pointer<operation_node, 2, QueueState> m_queue = { nullptr, NotResuming_NoPending };
        intptr_t m_readerLockCount = 0;
    };

    static constexpr intptr_t WriteLockAcquiredLockCount = intptr_t(-1);

    double_wide_atomic<double_wide_value<state>> m_state;
    operation_node* m_pending = nullptr;
    operation_node** m_pendingTail = &m_pending;
    
    class operation
        :
    public operation_node
    {
    protected:
        basic_async_reader_writer_lock& m_lock;
        using operation_node::m_next;
        using operation_node::m_continuation;
        using operation_node::m_operationType;
    private:
        friend class basic_async_reader_writer_lock;

        operation(
            basic_async_reader_writer_lock& lock,
            operation_type operationType
        ) :
            m_lock{ lock }
        {
            m_operationType = operationType;
        }

    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        bool await_suspend(
            auto continuation
        )
        {
            double_wide_value previousState = m_lock.m_state.load_inconsistent();
            double_wide_value nextState{ state{} };
            bool suspended;

            do
            {
                auto queueState = previousState->m_queue.tag();
                auto queue = previousState->m_queue.value();
                auto readerCount = previousState->m_readerLockCount;

                if (queueState == NotResuming_NoPending
                    && !queue
                    && readerCount >= 0
                    && m_operationType == operation_type::read)
                {
                    suspended = false;
                    nextState = state
                    {
                        .m_queue = { nullptr, NotResuming_NoPending },
                        .m_readerLockCount = readerCount + 1,
                    };
                }
                else if (
                    queueState == NotResuming_NoPending
                    && !queue
                    && readerCount == 0
                    && m_operationType == operation_type::write)
                {
                    suspended = false;
                    nextState = state
                    {
                        .m_queue = { nullptr, NotResuming_NoPending },
                        .m_readerLockCount = WriteLockAcquiredLockCount,
                    };
                }
                else
                {
                    suspended = true;
                    m_next = queue;
                    nextState = state
                    {
                        .m_queue = { this, queueState, },
                        .m_readerLockCount = readerCount,
                    };
                }
            } while (!m_lock.m_state.compare_exchange_weak(
                previousState,
                nextState
            ));

            if (suspended)
            {
                m_continuation = continuation;
            }

            return suspended;
        }

        void await_resume() const noexcept
        {}
    };

    void unlock(
        intptr_t readerCountChange)
    {
        double_wide_value previousState = m_state.load_inconsistent();
        QueueState previousQueueState;
        operation_node* queue;
        intptr_t readerCount;
        bool resumeLocks;

        double_wide_value resumingState{ state{} };
        do
        {
            queue = previousState->m_queue.value();
            previousQueueState = previousState->m_queue.tag();
            readerCount = previousState->m_readerLockCount + readerCountChange;
            resumingState->m_readerLockCount = readerCount;

            if ((previousQueueState & QueueState::IsResumingMask)
                ||
                (!queue && !(previousQueueState & QueueState::HasPendingMask))
                || 
                (readerCount > 0))
            {
                resumingState->m_queue = previousState->m_queue;
                resumeLocks = false;
            }
            else
            {
                resumingState->m_queue = { nullptr, IsResuming_NoPending };
                resumeLocks = true;
            }
        } while (!m_state.compare_exchange_weak(
            previousState,
            resumingState
        ));

        if (!resumeLocks)
        {
            return;
        }

        intptr_t locksToResumeCount = 0;
        operation_node* locksToResume = nullptr;
        operation_node* lastLockToResume = nullptr;

        queue = previousState->m_queue.value();

    CollectPendingItems:
        readerCount = resumingState->m_readerLockCount;

        // Move all the queue items to the pending list,
        // reversing the queue in the process.
        operation_node* previous = nullptr;

        auto newPendingTail = queue ? &queue->m_next : m_pendingTail;
        while (queue)
        {
            auto next = queue->m_next;
            queue->m_next = previous;
            previous = queue;
            *m_pendingTail = queue;
            queue = next;
        }
        m_pendingTail = newPendingTail;

        if (lastLockToResume
            && lastLockToResume->m_next == nullptr)
        {
            lastLockToResume->m_next = m_pending;
        }

        if (!locksToResume)
        {
            locksToResume = m_pending;
            lastLockToResume = nullptr;
        }

        // Now collect a set of awaiters to resume.
        while (
            m_pending
            &&
            (
                (
                    (readerCount >= 0)
                    && m_pending->m_operationType == operation_type::read
                    && locksToResume->m_operationType == operation_type::read
                    )
                ||
                (
                    readerCount == 0
                    && locksToResume == m_pending
                    && m_pending->m_operationType == operation_type::write)
                )
            )
        {
            lastLockToResume = m_pending;
            m_pending = m_pending->m_next;
            if (!m_pending)
            {
                m_pendingTail = &m_pending;
            }
            ++locksToResumeCount;
        }

        // Now locksToResume is a linked list that ends at m_pending
        // containing the awaiters to resume.
        bool needToReReadQueue = false;
        double_wide_value resumedState{ state{} };
        auto endOfUnlockList = m_pending;
        do
        {
            if (
                resumingState->m_queue.value()
                || resumingState->m_readerLockCount != readerCount
                )
            {
                needToReReadQueue = true;
                resumedState->m_queue = { nullptr, IsResuming_NoPending };
                resumedState->m_readerLockCount = resumingState->m_readerLockCount;
            }
            else if (
                locksToResume != endOfUnlockList)
            {
                needToReReadQueue = false;
                resumedState->m_queue = { nullptr, m_pending ? NotResuming_HasPending : NotResuming_NoPending };
                if (locksToResume->m_operationType == operation_type::write)
                {
                    resumedState->m_readerLockCount = WriteLockAcquiredLockCount;
                }
                else
                {
                    resumedState->m_readerLockCount = readerCount + locksToResumeCount;
                }
            }
            else
            {
                needToReReadQueue = false;
                resumedState->m_queue = { nullptr, m_pending ? NotResuming_HasPending : NotResuming_NoPending };
                resumedState->m_readerLockCount = resumingState->m_readerLockCount;
            }
        } while (!m_state.compare_exchange_weak(
            resumingState,
            resumedState
        ));

        if (needToReReadQueue)
        {
            queue = resumingState->m_queue.value();
            goto CollectPendingItems;
        }

        assert(resumingState->m_queue.tag()& IsResumingMask);
        assert(!(resumedState->m_queue.tag() & IsResumingMask));
        assert(!resumedState->m_queue.value() || resumedState->m_readerLockCount == WriteLockAcquiredLockCount);

        // Add all the entries to the thread-local resuming list.
        static thread_local operation_node* tls_resumingList = nullptr;
        static thread_local bool tls_resuming = false;

        bool alreadyResuming = tls_resuming;

        while (locksToResume != endOfUnlockList)
        {
            auto next = locksToResume->m_next;
            locksToResume->m_next = tls_resumingList;
            tls_resumingList = locksToResume;
            locksToResume = next;
        }

        // If we are the top-level resumer, resume.
        if (!alreadyResuming)
        {
            tls_resuming = true;
            while (tls_resumingList)
            {
                auto itemToResume = tls_resumingList;
                tls_resumingList = tls_resumingList->m_next;
                itemToResume->m_continuation.resume();
            }
            tls_resuming = false;
        }
    }

    class read_lock_operation;
    class write_lock_operation;

    class read_lock_operation : public operation
    {
        friend class basic_async_reader_writer_lock;
    protected:
        read_lock_operation(
            basic_async_reader_writer_lock& lock
        ) : operation
        {
            lock,
            operation_type::read,
        }
        {}
    };

    class read_lock_scoped_operation
        :
        public read_lock_operation
    {
        friend class basic_async_reader_writer_lock;
        using read_lock_operation::read_lock_operation;
        using read_lock_operation::m_lock;

    public:
        auto await_resume() noexcept
        {
            return read_lock{ m_lock.m_reader, std::adopt_lock };
        }
    };

    class write_lock_operation : public operation
    {
        friend class basic_async_reader_writer_lock;
    protected:
        write_lock_operation(
            basic_async_reader_writer_lock& lock
        ) : operation
        {
            lock,
            operation_type::write,
        }
        {}
    };

    class write_lock_scoped_operation : public write_lock_operation
    {
        friend class basic_async_reader_writer_lock;
        using write_lock_operation::write_lock_operation;
        using write_lock_operation::m_lock;

    public:
        auto await_resume() noexcept
        {
            return write_lock{ m_lock.m_writer, std::adopt_lock };
        }
    };

public:
    basic_async_reader_writer_lock() : 
        m_reader{ *this },
        m_writer{ *this }
    {
    }

    class reader_lock :
        public immovable_object
    {
        friend class basic_async_reader_writer_lock;
        basic_async_reader_writer_lock& m_lock;

        reader_lock(
            basic_async_reader_writer_lock& lock
        ) noexcept :
            m_lock { lock }
        {}
    
    public:
        void unlock() noexcept
        {
            m_lock.unlock(-1);
        }

        auto lock_async() noexcept
        {
            return read_lock_operation{ m_lock };
        }

        bool try_lock() noexcept
        {
            auto expectedState = m_lock.m_state.load_inconsistent();
            while (expectedState->m_readerLockCount >= 0)
            {
                auto desiredStateIsLockedForRead = expectedState;
                desiredStateIsLockedForRead->m_readerLockCount++;

                if (m_lock.m_state.compare_exchange_strong(
                    expectedState,
                    desiredStateIsLockedForRead))
                {
                    return true;
                }
            }

            return false;
        }

        auto scoped_lock_async() noexcept
        {
            return read_lock_scoped_operation{ m_lock };
        }

        auto try_scoped_lock() noexcept
        {
            if (try_lock())
            {
                return read_lock{ *this, std::adopt_lock };
            }
            else
            {
                return read_lock{};
            }
        }
    };

    class writer_lock :
        public immovable_object
    {
        friend class basic_async_reader_writer_lock;
        basic_async_reader_writer_lock& m_lock;
        
        writer_lock(
            basic_async_reader_writer_lock& lock
        ) noexcept :
            m_lock{ lock }
        {}

    public:
        void unlock() noexcept
        {
            m_lock.unlock(1);
        }

        auto lock_async() noexcept
        {
            return write_lock_operation{ m_lock };
        }

        bool try_lock() noexcept
        {
            auto expectedState = m_lock.m_state.load_inconsistent();
            auto desiredStateIsLockedForWrite = expectedState;
            desiredStateIsLockedForWrite->m_readerLockCount = WriteLockAcquiredLockCount;

            return expectedState->m_readerLockCount == 0
                && m_lock.m_state.compare_exchange_strong(
                    expectedState,
                    desiredStateIsLockedForWrite
                );
        }

        auto scoped_lock_async() noexcept
        {
            return write_lock_scoped_operation{ m_lock };
        }

        auto try_scoped_lock() noexcept
        {
            if (try_lock())
            {
                return write_lock{ *this, std::adopt_lock };
            }
            else
            {
                return write_lock{};
            }
        }
    };

    using read_lock = std::unique_lock<reader_lock>;
    using write_lock = std::unique_lock<writer_lock>;

    auto& reader() noexcept
    {
        return m_reader;
    }

    auto& writer() noexcept
    {
        return m_writer;
    }

private:
    reader_lock m_reader;
    writer_lock m_writer;
};

}
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::async_reader_writer_lock;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_async_reader_writer_lock_policy;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_async_reader_writer_lock;

}
#endif
