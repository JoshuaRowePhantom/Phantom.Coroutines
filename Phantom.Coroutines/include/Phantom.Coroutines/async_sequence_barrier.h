#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/fibonacci_heap.h"
#include "detail/immovable_object.h"
#include "policies.h"
#include <concepts>
#include <limits>

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
    using value_type = Value;
    using atomic_value_type = std::atomic<value_type>;

    class awaiter;
    struct awaiter_heap_builder;

    atomic_value_type m_lowestUnpublishedValue;
    std::atomic<awaiter*> m_queuedAwaiters;
    std::atomic<awaiter*> m_awaitersHeap;
    awaiter_heap_builder m_heapBuilder;

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
                std::memory_order_release,
                std::memory_order_relaxed
            ));

            // Double check to see if the value has been published.
            auto lowestUnpublishedValue = m_sequenceBarrier->basic_async_sequence_barrier::m_lowestUnpublishedValue.load(
                std::memory_order_acquire
            );

            if (m_sequenceBarrier->is_published(
                lowestUnpublishedValue,
                m_lowestUnpublishedValue))
            {
                m_lowestUnpublishedValue = lowestUnpublishedValue;

                // Try to resume awaiters,
                // and if we in particular desire to resume this object,
                // do not suspend.
                bool resumeThisAwaiter = false;

                m_sequenceBarrier->basic_async_sequence_barrier::resume_awaiters(
                    lowestUnpublishedValue,
                    this,
                    resumeThisAwaiter
                );

                return resumeThisAwaiter;
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
        value_type& lowestUnpublishedValue,
        awaiter* specialAwaiter,
        bool& resumeSpecialAwaiter
    )
    {
        resumeSpecialAwaiter = false;
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

            // Put back the heap if we can
            oldAwaitersHeap = nullptr;
            if (newAwaitersHeap != nullptr
                &&
                !self.basic_async_sequence_barrier::m_awaitersHeap.compare_exchange_strong(
                    oldAwaitersHeap,
                    newAwaitersHeap,
                    std::memory_order_release,
                    std::memory_order_relaxed))
            {
                // If we couldn't put the heap back,
                // then there's another heap that we might
                // need to trigger the awaiters of.
                // We'll pull it and ask it.
                continue;
            }

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
                auto nextAwaiter = awaitersToResume->m_siblingPointer;
                if (awaitersToResume == specialAwaiter)
                {
                    resumeSpecialAwaiter = true;
                }
                else
                {
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

    void publish(
        this auto& self,
        value_type value
    ) noexcept
    {
        auto lowestUnpublishedValue = value + 1;
        
        self.basic_async_sequence_barrier::m_lowestUnpublishedValue.store(
            lowestUnpublishedValue,
            std::memory_order_release
        );

        bool resumeSpecialAwaiter;
        self.basic_async_sequence_barrier::resume_awaiters(
            lowestUnpublishedValue,
            nullptr,
            resumeSpecialAwaiter
        );
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
};
}

using detail::async_sequence_barrier;
}
