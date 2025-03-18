#pragma once
#include "async_reader_writer_lock.h"
#include "direct_initialized_optional.h"
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/immovable_object.h"
#include "Phantom.Coroutines/detail/scope_guard.h"
#else
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.scope_guard;
#endif
#include "sharding.h"

namespace Phantom::Coroutines
{

namespace detail
{
class basic_async_sharded_reader_writer_lock_continuation;
}

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_sharded Sharded
>
class basic_async_sharded_reader_writer_lock;

template<
    typename T
> concept is_basic_async_sharded_reader_writer_lock_policy =
is_await_cancellation_policy<T>
|| is_concrete_policy<T, noop_on_destroy>
|| is_concrete_policy<T, fail_on_destroy_with_awaiters>
// Cardinality policies aren't useful for reader / writer locks
// || is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>;

template<
    is_basic_async_sharded_reader_writer_lock_policy ... Policy
> using underlying_sharded_reader_writer_lock =
async_reader_writer_lock<
    continuation_type<detail::basic_async_sharded_reader_writer_lock_continuation>,
    Policy...
>;

template<
    is_basic_async_sharded_reader_writer_lock_policy ... Policy
> using async_sharded_reader_writer_lock = basic_async_sharded_reader_writer_lock<
    select_await_cancellation_policy<Policy..., await_is_not_cancellable>,
    select_continuation_type<Policy..., default_continuation_type>,
    static_cache_aligned_sharded_array<
        underlying_sharded_reader_writer_lock<Policy...>
    >
>;

namespace detail
{
struct basic_async_sharded_reader_writer_lock_operation_base
{
    virtual void resume() noexcept = 0;
};

class basic_async_sharded_reader_writer_lock_continuation
{
    template<
        is_await_cancellation_policy,
        is_continuation Continuation,
        is_sharded Sharded
    >
    friend class basic_async_sharded_reader_writer_lock;

    basic_async_sharded_reader_writer_lock_operation_base* m_operation;

public:
    basic_async_sharded_reader_writer_lock_continuation(
        basic_async_sharded_reader_writer_lock_operation_base* operation = nullptr
    ) : m_operation{ operation }
    {}

    void resume() noexcept
    {
        m_operation->resume();
    }
};

}

template<
    is_await_cancellation_policy AwaitCancellationPolicy,
    is_continuation Continuation,
    is_sharded ReaderWriterLockShards
>
class basic_async_sharded_reader_writer_lock
    : 
    private detail::immovable_object
{
    static constexpr bool is_cancellable = is_concrete_policy<
        AwaitCancellationPolicy,
        await_is_cancellable>;

    ReaderWriterLockShards m_locks;

    using async_reader_writer_lock_type = std::remove_reference_t<decltype(m_locks.get_current_shard())>;

    class scoped_read_lock_operation
        :
        private detail::basic_async_sharded_reader_writer_lock_operation_base
    {
        friend class reader_lock;

        using operation_type = decltype(
            std::declval<typename async_reader_writer_lock_type::reader_lock&>().scoped_lock_async()
            );

        operation_type m_operation;
        Continuation m_continuation;

        void resume() noexcept override
        {
            m_continuation.resume();
        }

        scoped_read_lock_operation(
            async_reader_writer_lock_type& lock
        ) :
            m_operation{ lock.reader().scoped_lock_async() }
        {}

    public:
        bool await_ready() const noexcept
        {
            return m_operation.await_ready();
        }

        bool await_suspend(
            Continuation continuation
        ) noexcept
        {
            m_continuation = continuation;
            return m_operation.await_suspend(detail::basic_async_sharded_reader_writer_lock_continuation{ this });
        }

        auto await_resume() noexcept
        {
            return m_operation.await_resume();
        }
    };

    // If wait operations are cancellable, then it's possible
    // to roll back a lock acquisition.
    // That means we hold onto scoped_lock instances
    // for each lock acquired until the 
    // operation is committed and will no longer be rolled back.
    template<
        bool is_cancellable
    >
    struct write_lock_operation_acquired_locks
    {
        using acquired_locks_type = decltype(create_shards<typename async_reader_writer_lock_type::write_lock>(m_locks));
        acquired_locks_type m_acquiredLocks;

        write_lock_operation_acquired_locks(
            is_sharded auto& locks
        ) :
            m_acquiredLocks{ create_shards<typename async_reader_writer_lock_type::write_lock>(locks) }
        {}

        auto acquire_lock_operation(
            is_sharded auto& locks,
            size_t shardIndex)
        {
            return get_shards(locks)[shardIndex].writer().scoped_lock_async();
        }

        using operation_type = decltype(acquire_lock_operation(std::declval<basic_async_sharded_reader_writer_lock>(), 0));

        void resume_acquire_lock_operation(
            size_t shardIndex,
            auto& operation
        )
        {
            m_acquiredLocks[shardIndex] = operation.await_resume();
        }

        void commit_locks()
        {
            // Each scoped_lock can now be released _without_ unlocking it.
            for (auto& lock : m_acquiredLocks)
            {
                lock.release();
            }
        }
    };

    // If wait operations are not cancellable, then it's never possible
    // to roll back a lock acquisition.
    // That means we don't need to hold onto scoped_lock instances
    // for each lock acquired.
    template<
    >
    struct write_lock_operation_acquired_locks<
        false
    >
    {
        write_lock_operation_acquired_locks(
            is_sharded auto& locks
        )
        {
            std::ignore = locks;
        }

        static auto acquire_lock_operation(
            is_sharded auto& locks,
            size_t shardIndex)
        {
            return get_shards(locks)[shardIndex].writer().lock_async();
        }

        using operation_type = decltype(acquire_lock_operation(std::declval<ReaderWriterLockShards&>(), 0));

        static void resume_acquire_lock_operation(
            size_t /* shardIndex */,
            auto& operation
        )
        {
            operation.await_resume();
        }

        static void commit_locks()
        {
        }
    };

    class write_lock_operation
        :
        private detail::basic_async_sharded_reader_writer_lock_operation_base,
        private write_lock_operation_acquired_locks<is_cancellable>
    {
        friend class writer_lock;

        using typename write_lock_operation_acquired_locks<is_cancellable>::operation_type;
        using write_lock_operation_acquired_locks<is_cancellable>::acquire_lock_operation;
        using write_lock_operation_acquired_locks<is_cancellable>::resume_acquire_lock_operation;
        using write_lock_operation_acquired_locks<is_cancellable>::commit_locks;

    protected:
        basic_async_sharded_reader_writer_lock& m_lock;
    
    private:
        size_t m_lockIndex = 0;
        direct_initialized_optional<operation_type> m_operation;
        Continuation m_continuation;

        write_lock_operation(
            basic_async_sharded_reader_writer_lock& lock
        ) noexcept
            :
            write_lock_operation_acquired_locks<is_cancellable>{ lock.m_locks },
            m_lock{ lock }
        {}

        // Try to acquire the remaining locks.
        // Return true to suspend the operation, false to resume it.
        bool acquire_locks_or_suspend() noexcept
        {
            for (; m_lockIndex < get_shard_count(m_lock.m_locks); m_lockIndex++)
            {
                m_operation.emplace([&] { return acquire_lock_operation(m_lock.m_locks, m_lockIndex); });
                if (!m_operation->await_ready())
                {
                    if (m_operation->await_suspend(detail::basic_async_sharded_reader_writer_lock_continuation{ this }))
                    {
                        return true;
                    }
                    resume_acquire_lock_operation(
                        m_lockIndex,
                        *m_operation
                    );
                }
                m_operation.reset();
            }

            return false;
        }

        void resume() noexcept override
        {
            resume_acquire_lock_operation(
                m_lockIndex,
                *m_operation
            );

            m_operation.reset();
            m_lockIndex++;

            if (!acquire_locks_or_suspend())
            { 
                m_continuation.resume();
            }
        }

    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        bool await_suspend(
            Continuation continuation
        ) noexcept
        {
            m_continuation = continuation;
            return acquire_locks_or_suspend();
        }

        void await_resume() noexcept
        {
            commit_locks();
        }
    };


public:
    class writer_lock;

    using read_lock = typename async_reader_writer_lock_type::read_lock;
    using write_lock = std::unique_lock<writer_lock>;

    class reader_lock :
        public immovable_object
    {
        friend class basic_async_sharded_reader_writer_lock;
        basic_async_sharded_reader_writer_lock& m_lock;

        reader_lock(
            basic_async_sharded_reader_writer_lock& lock
        ) noexcept :
            m_lock{ lock }
        {}

    public:
        auto try_scoped_lock(
        ) noexcept
        {
            return try_scoped_lock(
                get_current_shard(m_lock.m_locks)
            );
        }

        auto try_scoped_lock(
            async_reader_writer_lock_type& shard
        ) noexcept
        {
            return shard.reader().try_scoped_lock();
        }

        auto scoped_lock_async(
        ) noexcept
        {
            return scoped_lock_async(
                get_current_shard(m_lock.m_locks)
            );
        }

        auto scoped_lock_async(
            async_reader_writer_lock_type& shard
        ) noexcept
        {
            return scoped_read_lock_operation{ shard };
        }
    };
    
    class writer_lock :
        public immovable_object
    {
        friend class basic_async_sharded_reader_writer_lock;
        basic_async_sharded_reader_writer_lock& m_lock;

        writer_lock(
            basic_async_sharded_reader_writer_lock& lock
        ) noexcept :
            m_lock{ lock }
        {}

    public:
        [[nodiscard]] auto try_lock() noexcept
        {
            bool complete = false;
            size_t lockIndex;
            detail::scope_guard guard = [&]()
            {
                if (!complete)
                {
                    for (size_t unlockIndex = 0; unlockIndex < lockIndex; ++unlockIndex)
                    {
                        get_shards(m_lock.m_locks)[unlockIndex].writer().unlock();
                    }
                }
            };

            for (lockIndex = 0; lockIndex < get_shard_count(m_lock.m_locks); lockIndex++)
            {
                if (!get_shards(m_lock.m_locks)[lockIndex].writer().try_lock())
                {
                    return false;
                }
            }

            complete = true;
            return true;
        }

        [[nodiscard]] auto try_scoped_lock() noexcept
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

        [[nodiscard]] auto lock_async() noexcept
        {
            return write_lock_operation{ m_lock };
        }

        [[nodiscard]] auto scoped_lock_async() noexcept
        {
            return scoped_write_lock_operation{ m_lock };
        }

        void unlock() noexcept
        {
            for (auto& lock : get_shards(m_lock.m_locks))
            {
                lock.writer().unlock();
            }
        }
    };

    basic_async_sharded_reader_writer_lock()
        : 
        m_reader{ *this },
        m_writer{ *this }
    {}

    auto& reader() noexcept
    {
        return m_reader;
    }

    auto& writer() noexcept
    {
        return m_writer;
    }

private:

    class scoped_write_lock_operation
        :
        public write_lock_operation
    {
        using write_lock_operation::m_lock;
    public:
        using write_lock_operation::write_lock_operation;

        write_lock await_resume() noexcept
        {
            write_lock_operation::await_resume();
            return write_lock{ m_lock.writer(), std::adopt_lock };
        }
    };

    reader_lock m_reader;
    writer_lock m_writer;
};

}
