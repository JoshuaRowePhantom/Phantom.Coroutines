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
#include "thread_local_storage.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    // The type of value to store.
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
        ) : 
            m_value { std::forward<decltype(args)>(args)... }
        {}
    };

    using soft_reference_type = value_holder*;
    using hard_reference_type =std::shared_ptr<value_holder> ;
    using atomic_hard_reference_type = std::atomic<hard_reference_type>;
    using sequence_number = size_t;
    using atomic_sequence_number = std::atomic<size_t>;

    class reference
    {
        hard_reference_type m_hardReference;
        soft_reference_type m_softReference = nullptr;

    public:
        reference(
            hard_reference_type hardReference
            ) noexcept
            :
            m_hardReference(std::move(hardReference)),
            m_softReference{ m_hardReference.get() }
        {
        }

        reference(
            soft_reference_type softReference = nullptr
        ) noexcept :
            m_softReference{ softReference }
        {
        }

        reference& operator=(
            reference&& other
        ) noexcept
        {
            m_hardReference = std::move(other.m_hardReference);
            m_softReference = other.m_softReference;
            other.m_softReference = nullptr;
            return *this;
        }
        
        reference& operator=(
            const reference& other
            ) noexcept = default;

        bool is_hard_reference() const noexcept
        {
            return m_hardReference.get() == m_softReference;
        }

        void make_hard_reference_to(
            const reference& other
        ) noexcept
        {
            make_hard_reference_to(other.m_hardReference);
        }

        void make_hard_reference_to(
            hard_reference_type other
        ) noexcept
        {
            m_hardReference = std::move(other);
            m_softReference = m_hardReference.get();
        }

        void make_soft_reference_to(
            const reference& other
        ) noexcept
        {
            m_hardReference = nullptr;
            m_softReference = other.m_softReference;
        }

        void make_soft_reference_to(
            const hard_reference_type& other
        ) noexcept
        {
            m_hardReference = nullptr;
            m_softReference = other.get();
        }

        void exchange(
            atomic_hard_reference_type& other
        ) noexcept
        {
            assert(is_hard_reference());
            m_hardReference = other.exchange(
                std::move(m_hardReference)
            );
            m_softReference = m_hardReference.get();
        }
        
        bool compare_exchange_strong(
            atomic_hard_reference_type& destination,
            reference&& desired
        ) noexcept
        {
            assert(is_hard_reference());
            assert(desired.is_hard_reference());

            bool result = destination.compare_exchange_strong(
                m_hardReference,
                desired.m_hardReference
            );
            m_softReference = m_hardReference.get();
            if (result)
            {
                swap(
                    *this,
                    desired);
            }

            return result;
        }
        
        auto operator==(
            soft_reference_type softReference
            ) const noexcept
        {
            return m_softReference == softReference;
        }
        
        auto operator==(
            const hard_reference_type& hardReference
            ) const noexcept
        {
            return m_softReference == hardReference.get();
        }

        auto operator==(
            const reference& other
            ) const noexcept
        {
            return m_softReference == other.m_softReference;
        }

        auto get() const noexcept
        {
            return m_softReference;
        }

        friend void swap(
            reference& left,
            reference& right
        ) noexcept
        {
            std::swap(left.m_hardReference, right.m_hardReference);
            std::swap(left.m_softReference, right.m_softReference);
        }
    };

    // This is the most recent value set on the section.
    atomic_hard_reference_type m_currentValueHardReference;

    // The sequence number is updated whenever m_currentValueHardReference is updated.
    // If the sequence number has changed, m_currentValueHardReference should be re-read.
    atomic_sequence_number m_sequenceNumber = 1;

    void updateSequenceNumber()
    {
        m_sequenceNumber.fetch_add(1, std::memory_order_seq_cst);
    }

    class operation_node;

    struct thread_state
    {
        hard_reference_type m_hardReference;
        sequence_number m_sequenceNumber = 0;
        
        // The head and tail exist to allow link() and unlink() to be
        // as simple as possible with no conditionals.
        operation_node m_operationsHead;
        operation_node m_operationsTail;

        thread_state()
            :
            m_operationsHead{ nullptr },
            m_operationsTail{ nullptr }
        {
            m_operationsHead.m_nextOperationInThread = &m_operationsTail;
            m_operationsTail.m_previousOperationInThread = &m_operationsHead;
        }
    };

    thread_local_storage<
        thread_state
    > m_threadState;

    class operation_node
    {
    public:
        operation_node(
            soft_reference_type initialValue
        ) :
            m_reference{ initialValue }
        { }

        reference m_reference;
        operation_node* m_nextOperationInThread = nullptr;
        operation_node* m_previousOperationInThread = nullptr;

        void link(
            thread_state& threadState
        ) noexcept
        {
            m_previousOperationInThread = &threadState.m_operationsHead;
            m_nextOperationInThread = threadState.m_operationsHead.m_nextOperationInThread;
            m_nextOperationInThread->m_previousOperationInThread = this;
            threadState.m_operationsHead.m_nextOperationInThread = this;
        }

        void unlink(
        ) noexcept
        {
            m_previousOperationInThread->m_nextOperationInThread = m_nextOperationInThread;
            m_nextOperationInThread->m_previousOperationInThread = m_previousOperationInThread;
        }

        void make_hard_reference_to(
            const hard_reference_type& hardReference) noexcept
        {
            m_reference.make_hard_reference_to(
                hardReference);
        }
    };

    class operation
        :
        protected assert_same_thread,
        private immovable_object
    {
    protected:
        read_copy_update_section& m_section;
        thread_state& m_threadState;
        operation_node m_node;

    private:
        bool need_refresh() const noexcept
        {
            return (m_section.m_sequenceNumber.load(
                std::memory_order_relaxed
            ) != m_threadState.m_sequenceNumber);
        }

    protected:
        operation(
            read_copy_update_section& section
        ) noexcept
            :
            m_section{ section },
            m_threadState{ section.m_threadState.get() },
            m_node{ m_threadState.m_hardReference.get() }
        {
            m_node.link(
                m_threadState
            );
            if (need_refresh()) [[unlikely]]
            {
                refresh();
            }
        }

        ~operation() noexcept
        {
            m_node.unlink();
        }

        [[msvc::forceinline]]
        bool refresh_thread_local_reference() noexcept
        {
            if (!need_refresh()) [[likely]]
            {
                return false;
            }

            m_threadState.m_sequenceNumber = m_section.m_sequenceNumber.load(
                std::memory_order_seq_cst
            );

            auto newHardReference = m_section.m_currentValueHardReference.load(
                std::memory_order_seq_cst);

            if (newHardReference == m_threadState.m_hardReference)
            {
                return false;
            }

            update_thread_local_references(
                m_threadState.m_hardReference);

            m_threadState.m_hardReference = std::move(newHardReference);

            return true;
        }

        [[msvc::noinline]]
        void update_thread_local_references(
            const hard_reference_type& oldHardReference
        ) noexcept
        {
            // We're going to replace the thread-local hard reference,
            // so make sure all other operations on the current thread
            // pointing at the same value holder get a hard reference.
            for (auto updatedOperation = m_threadState.m_operationsHead.m_nextOperationInThread;
                updatedOperation;
                updatedOperation = updatedOperation->m_nextOperationInThread)
            {
                if (updatedOperation->m_reference == oldHardReference)
                {
                    updatedOperation->make_hard_reference_to(
                        oldHardReference);
                }
            }
        }

        void make_hard_reference() noexcept
        {
            if (m_node.m_reference.is_hard_reference())
            {
                return;
            }

            // If the reference is a soft reference,
            // it must refere to the thread-local value.
            assert(m_node.m_reference == m_threadState.m_hardReference);

            m_node.m_reference.make_hard_reference_to(
                m_threadState.m_hardReference);
        }

    public:
        Value& value() noexcept
        {
            check_thread();
            return m_node.m_reference.get()->m_value;
        }

        // Read the value of the read_copy_update_section as
        // of the time the operation was started.
        Value* operator->() noexcept
        {
            return &value();
        }

        // Read the value of the read_copy_update_section as
        // of the time the operation was started.
        Value& operator*() noexcept
        {
            return value();
        }

        // Refresh the value to the latest stored in the section.
        // Returns true if the value changed.
        [[msvc::noinline]]
        bool refresh() noexcept
        {
            refresh_thread_local_reference();

            bool result = m_node.m_reference == m_threadState.m_hardReference;

            m_node.m_reference.make_soft_reference_to(
                m_threadState.m_hardReference.get());

            return result;
        }
    };

public:

    class read_operation
        :
        public operation
    {
    protected:
        using operation::m_section;
    public:
        read_operation(
            const read_copy_update_section& section
        ) noexcept :
            operation{ const_cast<read_copy_update_section&>(section) }
        {
        }
    };

    class update_operation
        :
        public read_operation
    {
    protected:
        using read_operation::m_section;
        using read_operation::m_threadState;
        using read_operation::m_node;
        using read_operation::make_hard_reference;
        using read_operation::update_thread_local_references;

    public:
        using read_operation::refresh;
        using read_operation::value;

    private:
        reference m_replacement;

    public:
        update_operation(
            read_copy_update_section& section
        ) noexcept :
            read_operation{ section }
        {}

        // Set the value to replace with.
        auto& operator=(
            auto&& value
            )
            requires std::constructible_from<Value, decltype(value)>
        {
            return emplace(
                std::forward<decltype(value)>(value)
            );
        }

        // Set the value to replace with.
        auto& emplace(
            auto&&... args
        )
            requires std::constructible_from<Value, decltype(args)...>
        {
            m_replacement.make_hard_reference_to(std::make_shared<value_holder>(
                std::forward<decltype(args)>(args)...
                ));

            return replacement();
        }

        // Perform the exchange.
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new value,
        // and replacement will become the old value.
        const Value& exchange() noexcept
        {
            operation::check_thread();

            assert(m_replacement.is_hard_reference());
            m_node.m_reference = m_replacement;
            m_replacement.exchange(
                m_section.m_currentValueHardReference
            );

            m_section.updateSequenceNumber();
            return value();
        }

        // Conditionally perform the exchange.
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new value of the read_copy_update_section,
        // and replacement becomes the old copy.
        // If the operation succeeds, replacement() becomes invalid,
        // otherwise replacement() is left alone.
        // Returns true if the exchange was successful, false if the exchange failed.
        bool compare_exchange_strong() noexcept
        {
            operation::check_thread();

            make_hard_reference();

            bool result = m_node.m_reference.compare_exchange_strong(
                m_section.m_currentValueHardReference,
                std::move(m_replacement)
            );

            if (result)
            {
                m_section.updateSequenceNumber();
            }

            return result;
        }

        // Obtain the value created by the previous operator=
        // or emplace operation. If there was no previous operation,
        // behavior is undefined.  
        [[nodiscard]]
        std::remove_const_t<Value>& replacement() noexcept
        {
            operation::check_thread();
            return m_replacement.get()->m_value;
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

        const Value& operator=(
            auto&& value
            )
            requires std::constructible_from<Value, decltype(value)...>
        {
            return emplace(
                std::forward<decltype(value)>(value)
            );
        }

        const Value& emplace(
            auto&&... args
        )
            requires std::constructible_from<Value, decltype(args)...>
        {
            update_operation::emplace(
                std::forward<decltype(args)>(args)...
            );

            return update_operation::exchange();
        }
    };

    read_copy_update_section(
        auto&&... args
    )
        requires std::constructible_from<Value, decltype(args)...>
    {
        auto currentValue = std::make_shared<value_holder>(
            std::forward<decltype(args)>(args)...
        );

        m_currentValueHardReference.store(
            std::move(currentValue),
            std::memory_order_release
        );
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
    //  read_copy_update_section<std::map<std::string, std::string>> section;
    // void AddEntryToMap(std::string key, std::string value)
    // {
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
    void emplace(
        auto&&... args
    )
        requires std::constructible_from<Value, decltype(args)...>
    {
        auto operation = write();
        operation.emplace(
            std::forward<decltype(args)>(args)...
        );
    }
};

}

using detail::read_copy_update_section;

}
