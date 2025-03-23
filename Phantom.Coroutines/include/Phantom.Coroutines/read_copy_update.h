#ifndef PHANTOM_COROUTINES_INCLUDE_READ_COPY_UPDATE_H
#define PHANTOM_COROUTINES_INCLUDE_READ_COPY_UPDATE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <concepts>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_set>
#include "detail/config.h"
#include "detail/assert_same_thread.h"
#include "detail/scope_guard.h"
#include "detail/immovable_object.h"
#include "nonatomic_shared_ptr.h"
#include "thread_local_storage.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

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
    using nonatomic_indirect_hard_reference_type = nonatomic_shared_ptr<hard_reference_type>;
    using nonatomic_hard_reference_type = nonatomic_shared_ptr<value_holder>;

    // This is the most recent value set on the section.
    atomic_hard_reference_type m_currentValueHardReference;

    // The sequence number is updated whenever m_currentValueHardReference is updated.
    // If the sequence number has changed, m_currentValueHardReference should be re-read.
    atomic_sequence_number m_sequenceNumber = 1;

    void updateSequenceNumber()
    {
        m_sequenceNumber.fetch_add(1, std::memory_order_seq_cst);
    }

    static nonatomic_hard_reference_type make_nonatomic_hard_reference(
        hard_reference_type hardReference
    )
    {
        auto indirectHardReference = make_nonatomic_shared<hard_reference_type>(
            std::move(hardReference));

        return nonatomic_hard_reference_type
        {
            std::move(indirectHardReference),
            indirectHardReference->get()
        };
    }

    class operation_node;

    struct thread_state
    {
        nonatomic_indirect_hard_reference_type m_indirectHardReference;
        nonatomic_hard_reference_type m_hardReference;
        sequence_number m_sequenceNumber = 0;

        void make_hard_reference_to(
            hard_reference_type hardReference
        )
        {
            m_indirectHardReference = make_nonatomic_shared<hard_reference_type>(
                std::move(hardReference));

            m_hardReference = nonatomic_hard_reference_type
            {
                m_indirectHardReference,
                m_indirectHardReference->get()
            };
        }
    };

    thread_local_storage<
        thread_state
    > m_threadState;

    class operation
        :
        protected assert_same_thread,
        private immovable_object
    {
    protected:
        read_copy_update_section& m_section;
        thread_state& m_threadState;
        nonatomic_hard_reference_type m_reference;

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
            m_reference{ m_threadState.m_hardReference }
        {
            if (need_refresh()) [[unlikely]]
            {
                refresh();
            }
        }

        PHANTOM_COROUTINES_MSVC_FORCEINLINE
        bool refresh_thread_local_reference() noexcept
        {
            if (!need_refresh()) [[likely]]
            {
                return false;
            }
            return force_refresh_thread_local_reference();
        }

        PHANTOM_COROUTINES_MSVC_FORCEINLINE
        bool force_refresh_thread_local_reference() noexcept
        {
            m_threadState.m_sequenceNumber = m_section.m_sequenceNumber.load(
                std::memory_order_seq_cst
            );

            auto newHardReference = m_section.m_currentValueHardReference.load(
                std::memory_order_seq_cst);

            if (newHardReference.get() == m_threadState.m_hardReference.get())
            {
                return false;
            }

            m_threadState.m_indirectHardReference = make_nonatomic_shared<hard_reference_type>(
                std::move(newHardReference)
            );
            m_threadState.m_hardReference = nonatomic_hard_reference_type
            {
                m_threadState.m_indirectHardReference,
                m_threadState.m_indirectHardReference->get()
            };

            return true;
        }
    public:
        Value& value() noexcept
        {
            check_thread();
            return m_reference->m_value;
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

            bool result = m_reference == m_threadState.m_hardReference;
            m_reference = m_threadState.m_hardReference;

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
        using read_operation::m_reference;
        using read_operation::force_refresh_thread_local_reference;

    public:
        using read_operation::refresh;
        using read_operation::value;

    private:
        hard_reference_type m_replacement;
        hard_reference_type m_original;

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
            m_replacement = std::make_shared<value_holder>(
                std::forward<decltype(args)>(args)...
            );

            return m_replacement->m_value;
        }

        // Perform a store operation
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new value,
        // and replacement and original will become empty.
        Value& store() noexcept
        {
            operation::check_thread();

            assert(m_replacement);
            
            m_threadState.make_hard_reference_to(
                std::move(m_replacement)
            );
            m_reference = m_threadState.m_hardReference;

            m_section.m_currentValueHardReference.store(
                *m_threadState.m_indirectHardReference
            );

            m_section.updateSequenceNumber();
            m_original.reset();

            return value();
        }
        
        // Perform the exchange.
        // using the value that was assigned or emplaced.
        // If there was no previous assignment or emplacement, behavior is undefined.
        // The value of the operator-> and operator* will be
        // updated to the new value,
        // and replacement will become empty,
        // and original will become the original value.
        Value& exchange() noexcept
        {
            operation::check_thread();

            assert(m_replacement);

            m_threadState.make_hard_reference_to(
                std::move(m_replacement)
            );
            m_reference = m_threadState.m_hardReference;

            m_original = m_section.m_currentValueHardReference.exchange(
                *m_threadState.m_indirectHardReference
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

            // Operations don't have hard_references to the value,
            // so we have to force a refresh to compute a value we can compare against.
            force_refresh_thread_local_reference();

            m_original = *m_threadState.m_indirectHardReference;

            // The new thread-local value might already indicate
            // that the compare-and-swap would fail.
            if (m_original.get() != m_reference.get())
            {
                m_reference = m_threadState.m_hardReference;
                return false;
            }

            if (m_section.m_currentValueHardReference.compare_exchange_strong(
                m_original,
                m_replacement))
            {
                m_section.updateSequenceNumber();

                assert(m_original.get() == m_threadState.m_indirectHardReference->get());
                m_reference = make_nonatomic_hard_reference(
                    std::move(m_replacement));
                m_replacement.reset();
                return true;
            }
            else
            {
                m_reference = m_threadState.m_hardReference;
                return false;
            }
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

        // Obtain the original value stored in the section
        // before any exchange or compare_exchange operation.
        // If no exchange operation has been done, 
        // behavior is undefined.
        [[nodiscard]]
        Value& original() const noexcept
        {
            return m_original->m_value;
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

            return update_operation::store();
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

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::read_copy_update_section;

}
#endif
