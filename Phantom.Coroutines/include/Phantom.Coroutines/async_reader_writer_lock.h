#pragma once

#include "policies.h"
#include "async_scope.h"
#include "async_auto_reset_event.h"
#include "reusable_task.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_await_result_on_destruction_policy AwaitResultOnDestructionPolicy,
    is_ordering_policy OrderingPolicy
>
class basic_async_reader_writer_lock;

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

template<
    is_async_reader_writer_lock_policy... Policies
> using async_reader_writer_lock = basic_async_reader_writer_lock<
    select_await_cancellation_policy<Policies..., await_is_not_cancellable>,
    select_continuation_type<Policies..., default_continuation_type>,
    select_await_result_on_destruction_policy<Policies..., noop_on_destroy>,
    select_ordering_policy<Policies..., fifo_ordering>
>;

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
    reader_lock m_reader = { *this };
    writer_lock m_writer = { *this };

    enum class operation_type
    {
        read,
        write
    };

    class operation;

    async_auto_reset_event<single_awaiter> m_operationsSignal;
    std::atomic<operation*> m_operations = nullptr;
    async_auto_reset_event<single_awaiter> m_pendingUnlockOperationCountSignal;
    std::atomic<size_t> m_pendingUnlockOperationCount = 0;

    class operation
    {
        friend class basic_async_reader_writer_lock;
        basic_async_reader_writer_lock& m_lock;
        operation_type m_operationType;
        operation* m_next;
        Continuation m_continuation;

        operation(
            basic_async_reader_writer_lock& lock,
            operation_type operationType
        ) :
            m_lock{ lock },
            m_operationType{ operationType }
        {}

    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        void await_suspend(
            auto continuation
        )
        {
            m_continuation = continuation;
            m_next = m_lock.m_operations.load(std::memory_order_relaxed);
            while (!m_lock.m_operations.compare_exchange_weak(
                m_next,
                this,
                std::memory_order_release
            ));

            // There's no need to set the event if m_next is non-zero:
            // the event is already set and the data hasn't been consumed.
            if (!m_next)
            {
                m_lock.m_operationsSignal.set();
            }
        }

        void await_resume() const noexcept
        {}
    };

    reusable_task<> acquisition_loop()
    {
        using enum operation_type;
        operation_type lastOperationType;
        operation* pendingOperations = nullptr;
        size_t runningOperationCount = 0;

        while (true)
        {
            if (!pendingOperations)
            {
                auto reversed = m_operations.exchange(
                    nullptr,
                    std::memory_order_acquire
                );

                // Reverse the list to provide FIFO order.
                while (reversed)
                {
                    auto next = reversed->m_next;
                    reversed->m_next = pendingOperations;
                    pendingOperations = reversed;
                    reversed = next;
                }
            }

            if (!pendingOperations)
            {
                co_await m_operationsSignal;
                continue;
            }

            while (pendingOperations)
            {
                if (runningOperationCount == 0
                    ||
                    lastOperationType == operation_type::read
                    && pendingOperations->m_operationType == operation_type::read)
                {
                    runningOperationCount++;

                    // The operation can be released!
                    // We have to copy the next pointer before resuming,
                    // as resuming destroys the operation.
                    auto nextOperation = pendingOperations->m_next;

                    // Whatever operation type just got released is the last operation type.
                    lastOperationType = pendingOperations->m_operationType;

                    pendingOperations->m_continuation.resume();
                    pendingOperations = nextOperation;
                }
                else
                {
                    // The latest operation could not be released because it is of
                    // the wrong type. Wait until some task completes.
                    co_await m_pendingUnlockOperationCountSignal;

                    auto pendingUnlockOperationCount = m_pendingUnlockOperationCount.exchange(
                        0,
                        // If the previous operation type was a write, we want to 
                        // acquire the memory released by the write.
                        // Otherwise we have no ordering restrictions.
                        lastOperationType == operation_type::write ? std::memory_order_acquire : std::memory_order_relaxed
                    );
                    runningOperationCount -= pendingUnlockOperationCount;
                }
            }

            // We have no more pending operations to process, so go back and wait for more.
        }
    }

    void unlock(
        operation_type operationType)
    {
        // If the previous operation type was a write, we want to 
        // release the memory written by the write operation.
        // Otherwise we have no ordering restrictions.
        // Also, we only need to signal the event if the fetch_add started from zero,
        // as otherwise the thread that first got zero will have signalled the event.
        if (0 ==
            m_pendingUnlockOperationCount.fetch_add(
                1,
                operationType == operation_type::write ? std::memory_order_release : std::memory_order_relaxed
            ))
        {
            m_pendingUnlockOperationCountSignal.set();
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

    async_scope<> m_acquisitionLoopScope;
    reusable_task<> m_acquisitionLoop = this->acquisition_loop();

public:
    basic_async_reader_writer_lock()
    {
        m_acquisitionLoopScope.spawn(
            m_acquisitionLoop);
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
            m_lock.unlock(
                operation_type::read);
        }

        auto lock_async() noexcept
        {
            return read_lock_operation{ m_lock };
        }

        auto scoped_lock_async() noexcept
        {
            return read_lock_scoped_operation{ m_lock };
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
            m_lock.unlock(
                operation_type::write);
        }

        auto lock_async() noexcept
        {
            return write_lock_operation{ m_lock };
        }

        auto scoped_lock_async() noexcept
        {
            return write_lock_scoped_operation{ m_lock };
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
};

}
using detail::async_reader_writer_lock;
using detail::is_async_reader_writer_lock_policy;

}