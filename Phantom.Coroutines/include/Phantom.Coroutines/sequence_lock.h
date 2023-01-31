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
    // m_sequenceNumber & 0x1 implies the value is in the process of being updated
    // m_sequenceNumber & 0x2 implies there was some waiter looking for m_sequenceNumber to be updated
    std::atomic<size_t> m_sequenceNumber;
    Value m_value;

    void wait(size_t& expectedSequenceNumber)
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
    Value read()
    {
        Value result;
        size_t expectedSequenceNumber;
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

    void write(Value value)
    {
        size_t expectedSequenceNumber, nextSequenceNumber;

        expectedSequenceNumber = m_sequenceNumber.load(std::memory_order_relaxed);
        
        while (expectedSequenceNumber & 0x3
            || !m_sequenceNumber.compare_exchange_weak(
                expectedSequenceNumber,
                expectedSequenceNumber + 1,
                std::memory_order_acquire))
        {
            if (expectedSequenceNumber & 0x3)
            {
                wait(expectedSequenceNumber);
                expectedSequenceNumber = m_sequenceNumber.load(std::memory_order_relaxed);
            }
        }
        
        nextSequenceNumber = expectedSequenceNumber + 4;
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
    }
};
}