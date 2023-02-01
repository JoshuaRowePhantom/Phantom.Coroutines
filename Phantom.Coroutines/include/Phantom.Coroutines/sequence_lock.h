#include <assert.h>
#include <atomic>
#include <type_traits>

namespace Phantom::Coroutines
{
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
        Value result;
        do
        {
            while ((expectedSequenceNumber = m_sequenceNumber.load(std::memory_order_acquire)) & 0x3)
            {
                wait(expectedSequenceNumber);
            }

            result = m_value;
        } while (expectedSequenceNumber != m_sequenceNumber.load(std::memory_order_acquire));
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
            expectedSequenceNumber + 1,
            std::memory_order_acquire
        ))
        {
            return false;
        }

        sequence_number nextSequenceNumber = expectedSequenceNumber + 4;
        expectedSequenceNumber += 1;
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
        size_t expectedSequenceNumber, nextSequenceNumber;

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