#ifndef PHANTOM_COROUTINES_INCLUDE_ASYNC_SEQUENCE_BARRIER_H
#define PHANTOM_COROUTINES_INCLUDE_ASYNC_SEQUENCE_BARRIER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <atomic>
#include <concepts>
#include <limits>
#include "detail/config.h"
#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/fibonacci_heap.h"
#include "detail/immovable_object.h"
#include "policies.h"
#else
import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.fibonacci_heap;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.policies;
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename Value,
    typename Less,
    typename Continuation
> class basic_async_sequence_barrier;

template<
    typename Policy
> concept is_async_sequence_barrier_policy =
is_continuation_type_policy<Policy>
|| is_concrete_policy<Policy, noop_on_destroy>
|| is_concrete_policy<Policy, fail_on_destroy_with_awaiters>
|| is_concrete_policy<Policy, awaiter_cardinality_policy>
|| is_concrete_policy<Policy, await_is_not_cancellable>;

template<
    typename Value = size_t,
    typename Comparer = std::less<Value>,
    is_async_sequence_barrier_policy ... Policies
> using async_sequence_barrier =
basic_async_sequence_barrier<
    Value,
    Comparer,
    select_continuation_type<Policies..., default_continuation_type>
>;

template<
    typename Value,
    typename Comparer,
    typename Continuation
> class basic_async_sequence_barrier
    :
    private immovable_object
{
public:
    using value_type = Value;
private:
    using atomic_value_type = std::atomic<value_type>;

    class awaiter;
    struct awaiter_heap_builder;

    static constexpr size_t maximumAwaiterDegree = std::numeric_limits<size_t>::digits;
    typedef size_t degree_type;

    bool is_published(
        Value lowestUnpublishedValue,
        Value valueToCheck
    )
    {
        return !m_heapBuilder.m_comparer(
            lowestUnpublishedValue,
            valueToCheck
        );
    }

    class awaiter
    {
        template<
            typename Value,
            typename Less,
            typename Continuation
        > friend class basic_async_sequence_barrier;

        value_type m_lowestUnpublishedValue;

        basic_async_sequence_barrier* m_sequenceBarrier;
        awaiter* m_siblingPointer;
        awaiter* m_subtreePointer = nullptr;
        degree_type m_degree = 0;
        Continuation m_continuation;

        // We atomically decrement this to resume the awaiter.
        // When the value reaches zero, we should be resumed.
        std::atomic<int> m_resumeCount = 2;

        awaiter(
            basic_async_sequence_barrier* sequenceBarrier,
            value_type lowestUnpublishedValue
        ) :
            m_sequenceBarrier{ sequenceBarrier },
            m_lowestUnpublishedValue{ lowestUnpublishedValue }
        {}

    public:
        bool await_ready() noexcept
        {
            auto lowestUnpublishedValue = m_sequenceBarrier->m_lowestUnpublishedValue.load(
                std::memory_order_acquire
            );

            if (m_sequenceBarrier->is_published(
                lowestUnpublishedValue,
                m_lowestUnpublishedValue))
            {
                m_lowestUnpublishedValue = lowestUnpublishedValue;
                return true;
            }

            return false;
        }

        bool await_suspend(
            auto continuation
        ) noexcept
        {
            m_continuation = continuation;

            auto requestedLowestUnpublishedValue = m_lowestUnpublishedValue;

            // Enqueue this awaiter into the linked list of awaiters.
            auto nextQueuedAwaiter = m_sequenceBarrier->basic_async_sequence_barrier::m_queuedAwaiters.load(
                std::memory_order_relaxed
            );

            do
            {
                m_siblingPointer = nextQueuedAwaiter;
            } while (!m_sequenceBarrier->basic_async_sequence_barrier::m_queuedAwaiters.compare_exchange_weak(
                nextQueuedAwaiter,
                this,
                std::memory_order_acq_rel,
                std::memory_order_relaxed
            ));

            // It's possible that some thread has now published a value that would cause us to resume.
            auto actualLowestUnpublishedValue = m_sequenceBarrier->m_lowestUnpublishedValue.load(
                std::memory_order_acquire
            );

            if (m_sequenceBarrier->is_published(
                actualLowestUnpublishedValue,
                requestedLowestUnpublishedValue))
            {
                m_sequenceBarrier->resume_awaiters(
                    actualLowestUnpublishedValue
                );
            }

            // When we reach here, we might need to resume if we're the last one to decrement
            // m_resumeCount.
            if (m_resumeCount.fetch_sub(
                    1,
                    std::memory_order_acquire
                ) == 1)
            {
                // We're the last one to decrement m_resumeCount, so we should resume.
                return false;
            }

            return true;
        }

        value_type await_resume() noexcept
        {
            return m_lowestUnpublishedValue - 1;
        }
    };

    struct awaiter_heap_builder
        :
        public fibonacci_heap_builder<awaiter*>
    {
        Comparer m_comparer;

        bool precedes(
            awaiter* left,
            awaiter* right
        )
        {
            return m_comparer(
                left->m_lowestUnpublishedValue,
                right->m_lowestUnpublishedValue);
        }

        static bool is_empty(
            awaiter* heap
        ) {
            return !heap;
        }

        static awaiter* empty()
        {
            return nullptr;
        }

        static awaiter** child(
            awaiter* heap)
        {
            return &heap->m_subtreePointer;
        }

        static awaiter** sibling(
            awaiter* heap)
        {
            return &heap->m_siblingPointer;
        }

        static size_t& degree(
            awaiter* heap)
        {
            return heap->m_degree;
        }
    };

    void resume_awaiters(
        this auto& self,
        value_type& lowestUnpublishedValue
    )
    {
        awaiter* awaitersToResume = nullptr;

        // Take ownership of the enqueued awaiters.
        // We only need to do this once, since any new queued awaiter after this step
        // that would need to be resumed will itself do this sequence on its thread.
        awaiter* newAwaitersHeap = self.basic_async_sequence_barrier::m_queuedAwaiters.exchange(
            nullptr,
            std::memory_order_acquire
        );

        while (true)
        {
            auto previousLowestUnpublishedValue = lowestUnpublishedValue;

            // Take ownership of the awaiters heap
            auto oldAwaitersHeap = self.basic_async_sequence_barrier::m_awaitersHeap.exchange(
                nullptr,
                std::memory_order_acquire
            );

            assert(self.basic_async_sequence_barrier::m_heapBuilder.is_canonical(
                oldAwaitersHeap));

            auto predicate = self.basic_async_sequence_barrier::m_heapBuilder.collect_predicate(
                &awaitersToResume,
                [&](awaiter* heap)
                {
                    return self.basic_async_sequence_barrier::is_published(
                        lowestUnpublishedValue,
                        heap->m_lowestUnpublishedValue
                    );
                });

            auto heapsToExtract = {
                oldAwaitersHeap,
                newAwaitersHeap
            };

            newAwaitersHeap = self.basic_async_sequence_barrier::m_heapBuilder.extract(
                std::move(predicate),
                std::move(heapsToExtract));

            assert(self.basic_async_sequence_barrier::m_heapBuilder.is_canonical(
                newAwaitersHeap));

            // Put back the heap if we can
            oldAwaitersHeap = nullptr;
            if (newAwaitersHeap != nullptr
                &&
                !self.basic_async_sequence_barrier::m_awaitersHeap.compare_exchange_strong(
                    oldAwaitersHeap,
                    newAwaitersHeap,
                    // We need acquire so that if we read any awaiters, we read any published value.
                    // We need release so that if we write the awaiters back, all threads can see the updated heap structure
                    std::memory_order_acq_rel,
                    std::memory_order_acquire))
            {
                // If we couldn't put the heap back,
                // then there's another heap that we might
                // need to trigger the awaiters of.
                // We'll pull it and ask it.
                continue;
            }

            // We've put back the new awaiter heap,
            // any future awaiters we service should come
            // from only the oldAwaitersHeap.
            newAwaitersHeap = nullptr;

            // Since we put back the heap, the current published value
            // may have changed while we had sole ownership of the heap.
            // If so, we might have put back heap
            // entries that are already resumable, so we have to go
            // through them again to see what is resumable.
            // We do the load now so that we don't stay in the loop
            // in case we have waiters to resume and that resumption
            // causes this thread to wait a long time.
            lowestUnpublishedValue = self.basic_async_sequence_barrier::m_lowestUnpublishedValue.load(
                std::memory_order_acquire
            );

            // Resume the resumable awaiters.  
            // We do this here so that we don't hold onto a list of awaiters
            // indefinitely while we resume some of them.
            // In other words, some other thread is free to resume the awaiters
            // we've put back onto the heap while we resume this list.
            while (awaitersToResume)
            {
                // resuming the awaiter might destroy it, so we collect the sibling pointer first.
                auto nextAwaiter = awaitersToResume->m_siblingPointer;
                if (awaitersToResume->m_resumeCount.fetch_sub(
                        1,
                        std::memory_order_acquire
                    ) == 1)
                {
                    // We're the last one to decrement m_resumeCount, so we should resume it.
                    awaitersToResume->m_continuation.resume();
                }
                awaitersToResume = nextAwaiter;
            }

            // Now check to see whether any of the awaiters we might have
            // put back are possibly resumable.  If they are, then
            // try the loop again.
            if (lowestUnpublishedValue == previousLowestUnpublishedValue)
            {
                break;
            }
        }

    }

public:
    explicit basic_async_sequence_barrier(
        value_type initialPublishedValue = -1,
        Comparer comparer = {}
    ) noexcept :
        m_lowestUnpublishedValue{ initialPublishedValue + 1 },
        m_heapBuilder
        {
            .m_comparer = { std::move(comparer) },
        }
    {}

    size_t publish(
        this auto& self,
        value_type value
    ) noexcept
    {
        auto nextLowestUnpublishedValue = value + 1;
        
        auto currentLowestUnpublishedValue = self.m_lowestUnpublishedValue.load(
            std::memory_order_acquire);

        do
        {
            if (nextLowestUnpublishedValue <= currentLowestUnpublishedValue)
            {
                return currentLowestUnpublishedValue - 1;
            }
        } while (!self.m_lowestUnpublishedValue.compare_exchange_strong(
            currentLowestUnpublishedValue,
            nextLowestUnpublishedValue,
            std::memory_order_acq_rel,
            std::memory_order_acquire
        ));

        self.basic_async_sequence_barrier::resume_awaiters(
            nextLowestUnpublishedValue
        );

        return nextLowestUnpublishedValue - 1;
    }

    awaiter wait_until_published(
        this auto& self,
        value_type value
    ) noexcept
    {
        return awaiter{ &self, value + 1 };
    }

    auto last_published() const noexcept
    {
        return m_lowestUnpublishedValue.load(
            std::memory_order_acquire
        ) - 1;
    }

private:
    atomic_value_type m_lowestUnpublishedValue;
    std::atomic<awaiter*> m_queuedAwaiters;
    std::atomic<awaiter*> m_awaitersHeap;
    awaiter_heap_builder m_heapBuilder;

};
}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::async_sequence_barrier;
}
#endif
