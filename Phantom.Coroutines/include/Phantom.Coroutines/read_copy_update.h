#pragma once

#include <atomic>
#include <concepts>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_map>
#include "detail/assert_same_thread.h"
#include "detail/scope_guard.h"
#include "detail/immovable_object.h"

namespace Phantom::Coroutines
{
namespace detail
{

class ReadCopyUpdate_CleanupOnWrite
{};

class ReadCopyUpdate_CleanupOnReadOrWrite
{};

template<
    typename Value
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
        mutable_value_type m_value;

        value_holder(
            auto&&... args
        ) : m_value { std::forward<decltype(args)>(args)... }
        {}
    };

    typedef value_holder* soft_reference_type;
    typedef std::shared_ptr<value_holder> hard_reference_type;
    typedef std::atomic<soft_reference_type> atomic_soft_reference_type;

    std::mutex m_mutex;
    hard_reference_type m_valueHolderHardReference;
    atomic_soft_reference_type m_valueHolderSoftReference;

    class operation
        :
        protected assert_same_thread,
        private immovable_object
    {
        static inline thread_local hard_reference_type m_threadLocalHardReference;
        static inline thread_local operation* m_operationsHead;

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
        soft_reference_type m_valueHolderSoftReference = nullptr;
        hard_reference_type m_valueHolderHardReference;

        operation(
            read_copy_update_section& section
        )
            :
            m_section{ section }
        {
            link();
            force_refresh(
                get_section_soft_reference());
        }

        ~operation()
        {
            unlink();
        }

        void refresh_thread_local_hard_reference_and_update_soft_reference(
            soft_reference_type threadLocalSoftReference
        )
        {
            // We're going to replace the thread-local hard reference,
            // so make sure all other operations on the current thread
            // pointing at the same value holder get a hard reference.
            for (auto updatedOperation = m_operationsHead; updatedOperation; updatedOperation = updatedOperation->m_nextOperation)
            {
                if (updatedOperation->m_valueHolderSoftReference == threadLocalSoftReference)
                {
                    updatedOperation->m_valueHolderHardReference = m_threadLocalHardReference;
                }
            }

            {
                std::scoped_lock lock{ m_section.m_mutex };
                m_threadLocalHardReference = m_section.m_valueHolderHardReference;
            }

            m_valueHolderSoftReference = m_threadLocalHardReference.get();
        }

        auto get_section_soft_reference()
        {
            return m_section.m_valueHolderSoftReference.load(std::memory_order_acquire);
        } 

        // Refresh the value to the latest stored in the section.
        void force_refresh(
            soft_reference_type    sectionSoftReference)
        {
            m_valueHolderHardReference = nullptr;
            m_valueHolderSoftReference = nullptr;

            soft_reference_type threadLocalSoftReference = m_threadLocalHardReference.get();
            if (threadLocalSoftReference == sectionSoftReference)
            {
                m_valueHolderSoftReference = threadLocalSoftReference;
                return;
            }

            refresh_thread_local_hard_reference_and_update_soft_reference(
                threadLocalSoftReference);
        }

    public:
        Value& value()
        {
            check_thread();
            return m_valueHolderSoftReference->m_value;
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
        void refresh()
        {
            auto sectionSoftReference = m_section.m_valueHolderSoftReference.load(std::memory_order_acquire);
            if (m_valueHolderSoftReference == sectionSoftReference)
            {
                return;
            }

            force_refresh(
                sectionSoftReference);
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
        hard_reference_type    m_replacementValueHolder = nullptr;

        void exchange(
            std::unique_lock<std::mutex> lock
        )
        {
            this->m_valueHolderSoftReference = m_replacementValueHolder.get();

            std::swap(
                this->m_section.m_valueHolderHardReference,
                m_replacementValueHolder);

            this->m_section.m_valueHolderSoftReference.store(
                this->m_section.m_valueHolderHardReference.get(),
                std::memory_order_relaxed);

            lock.unlock();

            // Reset the old hard references outside the lock.
            this->m_valueHolderHardReference.reset();
            m_replacementValueHolder.reset();
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
            m_replacementValueHolder = std::make_shared<value_holder>(
                std::forward<decltype(args)>(args)...
                );

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
                std::unique_lock{ this->m_section.m_mutex }
            );
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

            if (this->m_section.m_valueHolderSoftReference.load(std::memory_order_acquire) != this->m_valueHolderSoftReference)
            {
                this->refresh();
                return false;
            }

            std::unique_lock lock{ this->m_section.m_mutex };
            if (this->m_section.m_valueHolderHardReference.get() != this->m_valueHolderSoftReference)
            {
                lock.unlock();
                this->refresh();
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
            return m_replacementValueHolder->m_value;
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
        m_valueHolderHardReference{ std::make_shared<value_holder>(
            std::forward<decltype(args)>(args)...)
    },
        m_valueHolderSoftReference{ m_valueHolderHardReference.get() }
    {
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
