#pragma once

#include <atomic>
#include <concepts>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_set>
#include "detail/assert_same_thread.h"
#include "detail/scope_guard.h"
#include "detail/immovable_object.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    // The type of value to store.
    typename Value,
    // A distinguishing label to separate out the thread-local
    // variables from other instances of read_copy_update_section.
    typename Label = void
>
class read_copy_update_section
    :
private immovable_object
{
    typedef size_t epoch_type;

    typedef Value value_type;
    typedef std::remove_const_t<Value> mutable_value_type;

    struct value_holder
    {
        read_copy_update_section* const m_section;
        mutable_value_type m_value;

        value_holder(
            read_copy_update_section* section,
            auto&&... args
        ) : 
            m_section { section },
            m_value { std::forward<decltype(args)>(args)... }
        {}
    };

    typedef value_holder* soft_reference_type;
    typedef std::shared_ptr<value_holder> hard_reference_type;
    typedef std::atomic<soft_reference_type> atomic_soft_reference_type;

    struct reference
    {
        hard_reference_type m_hardReference;
        atomic_soft_reference_type m_softReference = nullptr;

        reference(
            hard_reference_type hardReference
            )
            :
            m_hardReference(std::move(hardReference))
        {
            m_softReference.store(m_hardReference.get(), std::memory_order_release);
        }

        reference(
            soft_reference_type softReference = nullptr)
        {
            m_softReference.store(softReference, std::memory_order_release);
        }

        // Prevent moving and copying.
        auto operator=(reference&&) = delete;

        void swap(
            reference& other
        )
        {
            std::swap(m_hardReference, other.m_hardReference);
            
            auto temp = other.m_softReference.load(std::memory_order_acquire);
            
            other.m_softReference.store(
                m_softReference.load(std::memory_order_acquire),
                std::memory_order_release);
            
            m_softReference.store(
                temp,
                std::memory_order_release);
        }

        void clear()
        {
            m_hardReference = nullptr;
            m_softReference.store(nullptr, std::memory_order_release);
        }

        void make_hard_reference_to(
            const reference& other
        )
        {
            make_hard_reference_to(other.m_hardReference);
        }

        void make_hard_reference_to(
            hard_reference_type other
        )
        {
            m_hardReference = std::move(other);
            m_softReference.store(
                m_hardReference.get(),
                std::memory_order_release
            );
        }

        void make_soft_reference_to(
            const reference& other
        )
        {
            m_hardReference = nullptr;
            m_softReference.store(
                other.m_softReference.load(std::memory_order_acquire),
                std::memory_order_release
            );
        }

        bool is_hard_reference_for(
            const read_copy_update_section* section
        ) const
        {
            return m_hardReference
                && m_hardReference->m_section == section;
        }

        auto operator==(
            soft_reference_type softReference
            ) const
        {
            return m_softReference.load(std::memory_order_acquire) == softReference;
        }

        auto operator==(
            const reference& other
            ) const
        {
            return m_softReference.load(std::memory_order_acquire) == other.m_softReference.load(std::memory_order_acquire);
        }

        auto convert_to_hard_reference(
            const reference& source
        )
        {
            assert(source.m_softReference == m_softReference);
            assert(source.m_hardReference.get() == m_softReference);
            m_hardReference = source.m_hardReference;
        }

        auto operator->() const
        {
            // The -> operator is only used on the local thread.
            return m_softReference.load(std::memory_order_relaxed);
        }

        auto get() const
        {
            return m_softReference.load(std::memory_order_acquire);
        }
    };

    // We use shared_ptr and copy it to the individual threads.
    struct global_state
    {
        // The mutex is global, because it controls access to all thread data
        std::mutex m_mutex;
        // The set of all existing thread hard references.
        std::unordered_set<reference*> m_threadReferences;
    };

    static inline std::shared_ptr<global_state> m_globalState = std::make_shared<global_state>();
    static inline thread_local std::shared_ptr<global_state> m_threadLocalGlobalState = m_globalState;

    reference m_currentValue;

    class operation
        :
        protected assert_same_thread,
        private immovable_object
    {
        static inline thread_local operation* m_operationsHead;

        struct thread_hard_reference_tracker
        {
            thread_hard_reference_tracker()
            {
                std::unique_lock lock { m_threadLocalGlobalState->m_mutex };
                m_threadLocalGlobalState->m_threadReferences.insert(&m_threadLocalReference);
            }

            void assertTracked()
            {}

            ~thread_hard_reference_tracker()
            {
                std::unique_lock lock { m_threadLocalGlobalState->m_mutex };
                m_threadLocalGlobalState->m_threadReferences.erase(&m_threadLocalReference);
            }
        };

        static inline thread_local thread_hard_reference_tracker m_threadReferenceTracker;

        operation* m_nextOperation = nullptr;
        operation* m_previousOperation = nullptr;

        void link()
        {
            m_nextOperation = m_operationsHead;
            m_operationsHead = this;
            if (m_nextOperation)
            {
                m_nextOperation->m_previousOperation = this;
            }
        }

        void unlink()
        {
            if (m_operationsHead == this)
            {
                m_operationsHead = this->m_nextOperation;
            }

            if (m_nextOperation)
            {
                m_nextOperation->m_previousOperation = m_previousOperation;
            }

            if (m_previousOperation)
            {
                m_previousOperation->m_nextOperation = m_nextOperation;
            }
        }

    protected:
        read_copy_update_section& m_section;
        reference m_reference;
        static inline thread_local reference m_threadLocalReference;

        operation(
            read_copy_update_section& section
        )
            :
            m_section{ section }
        {
            m_threadReferenceTracker.assertTracked();
            link();
            refresh();
        }

        ~operation()
        {
            unlink();
        }

        bool refresh_thread_local_reference(
            std::unique_lock<std::mutex>& lock,
            reference& valueToRelease)
        {
            if (m_section.m_currentValue == m_threadLocalReference)
            { 
                return false;
            }

            // We're going to replace the thread-local hard reference,
            // so make sure all other operations on the current thread
            // pointing at the same value holder get a hard reference.
            for (auto updatedOperation = m_operationsHead; updatedOperation; updatedOperation = updatedOperation->m_nextOperation)
            {
                if (updatedOperation->m_reference == m_threadLocalReference)
                {
                    updatedOperation->m_reference.convert_to_hard_reference(
                        m_threadLocalReference);
                }
            }

            if (!lock)
            {
                lock.lock();
            }

            valueToRelease.swap(
                m_threadLocalReference);

            m_threadLocalReference.make_hard_reference_to(
                m_section.m_currentValue);

            return true;
        }

        // Refresh the value to the latest stored in the section.
        // Returns true if the value changed.
        bool refresh(
            std::unique_lock<std::mutex>& lock,
            reference& valueToRelease)
        {
            refresh_thread_local_reference(
                lock,
                valueToRelease);

            // We can do this outside a lock because
            // we know that this thread's section is not being destroyed by contract,
            // and that the thread local reference won't be destroyed because this thread
            // is not destroying it, and the section won't be destroying it because the
            // section itself is not being destroyed.
            if (m_reference != m_threadLocalReference)
            {
                m_reference.make_soft_reference_to(
                    m_threadLocalReference);
                return true;
            }

            return false;
        }

    public:
        Value& value()
        {
            check_thread();
            return m_reference->m_value;
        }

        // Read the value of the read_copy_update_section as
        // of the time the operation was started.
        Value* operator->()
        {
            return &value();
        }

        // Read the value of the read_copy_update_section as
        // of the time the operation was started.
        Value& operator*()
        {
            return value();
        }

        // Refresh the value to the latest stored in the section.
        // Returns true if the value changed.
        bool refresh()
        {
            // Declare in this order so that
            // valueToRelease is destroyed after the lock is unlocked.
            // That way value destruction happens outside of locks.
            reference valueToRelease;
            std::unique_lock lock{ m_threadLocalGlobalState->m_mutex , std::defer_lock };
            return refresh(lock, valueToRelease);
        }
    };

public:

    class read_operation
        :
        public operation
    {
    public:
        read_operation(
            const read_copy_update_section& section
        ) :
            operation{ const_cast<read_copy_update_section&>(section) }
        {
        }
    };

    class update_operation
        :
        public read_operation
    {
        reference m_replacement;

        void exchange(
            std::unique_lock<std::mutex> lock
        )
        {
            assert(lock.owns_lock());

            reference oldValue;
            oldValue.swap(this->m_reference);
            reference oldThreadValue;

            this->m_section.m_currentValue.swap(
                m_replacement
            );

            // This updates all the other operations that may have
            // been using the thread-local reference to instead use a hard reference.
            this->refresh_thread_local_reference(
                lock,
                oldThreadValue
            );

            // Reset the old references outside the lock.
            lock.unlock();

            // This can be done outside the lock because the
            // section cannot be destroyed while there is an operation outstanding,
            // therefore nothing will try to destroy the thread local reference.
            this->m_reference.make_soft_reference_to(
                this->m_threadLocalReference
            );

            // This removes the reference to the old value that -was- in the section
            this->m_replacement.clear();

            // oldValue and oldThreadValue will be destroyed here,
            // removing the references that this instance and thread used
            // to have.
        }

    public:
        update_operation(
            read_copy_update_section& section
        ) :
            read_operation{ section }
        {}

        // Set the value to replace with.
        decltype(auto) operator=(
            auto&& value
            )
        {
            return (emplace(
                std::forward<decltype(value)>(value)
            ));
        }

        // Set the value to replace with.
        decltype(auto) emplace(
            auto&&... args
        )
        {
            m_replacement.make_hard_reference_to(std::make_shared<value_holder>(
                &this->m_section,
                std::forward<decltype(args)>(args)...
                ));

            return (replacement());
        }

        // Perform the exchange.
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new replacement value.
        void exchange()
        {
            exchange(
                std::unique_lock { m_threadLocalGlobalState->m_mutex });
        }

        // Conditionally perform the exchange.
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new replacement value if successful, 
        // or to the current value of the read_copy_update_section if failed.
        // Returns true if the exchange was successful, false if the exchange failed.
        [[nodiscard]]
        bool compare_exchange_strong()
        {
            operation::check_thread();

            // Declare in this order so that valueToRelease
            // is released outside the lock.
            reference valueToRelease;
            std::unique_lock lock{ m_threadLocalGlobalState->m_mutex };

            if (this->refresh(
                lock,
                valueToRelease))
            {
                return false;
            }

            exchange(
                std::move(lock));

            return true;
        }

        // Obtain the value created by the previous operator=
        // or emplace operation. If there was no previous operation,
        // behavior is undefined.  If a previous exchange or compare_exchange
        // succeeded, the behavior is undefined.
        [[nodiscard]]
        std::remove_const_t<Value>& replacement()
        {
            operation::check_thread();
            return m_replacement.m_hardReference->m_value;
        }
    };

    class write_operation
        :
    private update_operation
    {
    public:
        write_operation(
            read_copy_update_section& section
        ) :
            update_operation{ section }
        {}

        using update_operation::value;

        Value& operator=(
            auto&& value
            )
        {
            return emplace(
                std::forward<decltype(value)>(value)
            );
        }

        Value& emplace(
            auto&&... args
        )
        {
            update_operation::emplace(
                std::forward<decltype(args)>(args)...
            );

            update_operation::exchange();

            return update_operation::value();
        }
    };

    read_copy_update_section(
        auto&&... args
    ) :
        m_currentValue
    {
        std::make_shared<value_holder>(
            this,
            std::forward<decltype(args)>(args)...)
    }
    {
    }

    ~read_copy_update_section()
    {
        std::unique_lock lock { m_threadLocalGlobalState->m_mutex };
        for (auto threadHardReferencePointer : m_threadLocalGlobalState->m_threadReferences)
        {
            if (threadHardReferencePointer->is_hard_reference_for(this))
            {
                // We -know- that there are no operations for this section,
                // because the contract for users is that they must not
                // destroy a read_copy_update_section until all the
                // operations are complete.
                // Therefore, clearing the thread's hard reference
                // is legal.
                threadHardReferencePointer->clear();
            }
        }
    }

    // Read the current value stored in the section.
    // The value is only valid for the duration
    // of the expression.
    [[nodiscard]] read_operation operator->() const
    {
        return read();
    }

    // Read the current value stored in the section.
    // The value is only valid for the duration
    // of the expression.
    [[nodiscard]] Value& operator*()
    {
        return *read();
    }

    // Read the current value stored in the section.
    [[nodiscard]] read_operation read() const
    {
        return read_operation
        { 
            const_cast<read_copy_update_section&>(*this) 
        };
    }

    // Begin an operation to read / modify / write
    // the value stored in the section, with update
    // race detection.
    // 
    // A typical use is:
    // 
    // void AddEntryToMap(std::string key, std::string value)
    // {
    //    read_copy_update_section<std::map<std::string, std::string>> section;
    //    auto operation = section.update();
    //  
    // // Start by copying the original map.
    //  operation.emplace(operation.value());
    //  // Add the key / value of interest
    //  operation.replacement()[key] = value;
    // 
    //  while (!operation.compare_exchange_strong())
    //  {
    //       // If we fail to perform the replacement, then our updated map
    //       // is missing some entries or has some out of date entries.
    //       // Rather than copy the map over again, we modify it in-place,
    //       // as there are likely only a few entries updated. A better algorithm
    //       // iterates over both maps in parallel.
    //     for(auto value : operation.value())
    //     {
    //        if (!operation.replacement().contains(value.first)
    //            || operation.replacement()[value.first] != value.second)
    //        {
    //            operation.replacement()[value.first] = value.second;
    //        }
    //     }
    //       operation.replacement()[key] = value;
    //  }
    // }
    [[nodiscard]] update_operation update()
    {
        return update_operation
        {
            *this
        };
    }

    // Begin an operation to read / modify / write
    // the value stored in the section.
    [[nodiscard]] write_operation write()
    {
        return write_operation{ *this };
    }

    // Unconditionally replace the stored value.
    // If this thread loses any races, the operation
    // is retried until it succeeds.
    void emplace(
        auto&&... args
    )
    {
        auto operation = write();
        operation.emplace(
            std::forward<decltype(args)>(args)...
        );
    }
};

}
}
