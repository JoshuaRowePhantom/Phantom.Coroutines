#ifndef PHANTOM_COROUTINES_INCLUDE_SEQUENCE_LOCK_H
#define PHANTOM_COROUTINES_INCLUDE_SEQUENCE_LOCK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <atomic>
#include <cstddef>
#include <type_traits>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Value
> 
requires std::is_trivially_copyable_v<Value>
class sequence_lock
{
public:
    using sequence_number = size_t;

private:
    // m_sequenceNumber & 0x1 implies the value is in the process of being updated
    // m_sequenceNumber & 0x2 implies there was some waiter looking for m_sequenceNumber to be updated
    mutable std::atomic<sequence_number> m_sequenceNumber;
    Value m_value;

    void wait(sequence_number& expectedSequenceNumber) const noexcept
    {
        auto desiredSequenceNumber = expectedSequenceNumber | 0x2;

        if (m_sequenceNumber.compare_exchange_weak(
            expectedSequenceNumber,
            desiredSequenceNumber))
        { 
            m_sequenceNumber.wait(desiredSequenceNumber, std::memory_order_relaxed);
        }
    }

public:
    sequence_lock(
        const Value& value = {}
    ) : m_value { value }
    {}

    // Read the underlying value consistently,
    // and return the sequence number to use for compare_exchange_weak.
    Value read(
        sequence_number& expectedSequenceNumber
    ) const noexcept
    {
        sequence_number localExpectedSequenceNumber;
        sequence_number localActualSequenceNumber;

        Value result;
        do
        {
            while ((localExpectedSequenceNumber = m_sequenceNumber.load(std::memory_order_acquire)) & 0x3)
            {
                wait(localExpectedSequenceNumber);
            }

            result = m_value;

            std::atomic_thread_fence(
                std::memory_order_release);

            localActualSequenceNumber = m_sequenceNumber.load(std::memory_order_acquire);
        } while (localActualSequenceNumber != localExpectedSequenceNumber);

        expectedSequenceNumber = localActualSequenceNumber;

        return result;
    }

    // Read the underlying value consistently.
    Value read() const noexcept
    {
        size_t expectedSequenceNumber;
        return read(expectedSequenceNumber);
    }

    // Update the value if it has not already been updated by another thread.
    bool compare_exchange_weak(
        const Value& value,
        sequence_number& expectedSequenceNumber
    ) noexcept
    {
        assert((expectedSequenceNumber & 0x3) == 0);
        if (!m_sequenceNumber.compare_exchange_weak(
            expectedSequenceNumber,
            expectedSequenceNumber | 0x1,
            std::memory_order_acquire
        ))
        {
            return false;
        }

        sequence_number nextSequenceNumber = expectedSequenceNumber + 4;
        expectedSequenceNumber |= 0x1;
        m_value = value;

        // This cmpxchg will fail if some thread performed a wait() operation.
        if (!m_sequenceNumber.compare_exchange_weak(
            expectedSequenceNumber,
            nextSequenceNumber,
            std::memory_order_release))
        {
            // Some thread performed a wait() operation.
            // Wake all other threads up after storing.
            m_sequenceNumber.store(nextSequenceNumber, std::memory_order_release);
            m_sequenceNumber.notify_all();
        }

        expectedSequenceNumber = nextSequenceNumber;

        return true;
    }

    void write(
        const Value& value
    ) noexcept
    {
        size_t expectedSequenceNumber;

        expectedSequenceNumber = m_sequenceNumber.load(std::memory_order_relaxed);
        while ((expectedSequenceNumber & 0x3)
            || !compare_exchange_weak(value, expectedSequenceNumber))
        {
            if (expectedSequenceNumber & 0x3)
            {
                wait(expectedSequenceNumber);
                expectedSequenceNumber = m_sequenceNumber.load(std::memory_order_relaxed);
            }
        }
    }
};
}
#endif
