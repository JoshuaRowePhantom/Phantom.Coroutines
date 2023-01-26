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
> class basic_sequence_barrier;

template<
    typename Policy
> concept is_sequence_barrier_policy =
is_continuation_type_policy<Policy>
|| is_concrete_policy<Policy, noop_on_destroy>
|| is_concrete_policy<Policy, fail_on_destroy_with_awaiters>
|| is_concrete_policy<Policy, awaiter_cardinality_policy>
|| is_concrete_policy<Policy, await_is_not_cancellable>;

template<
    typename Value = size_t,
    typename Comparer = std::less<Value>,
    is_sequence_barrier_policy ... Policies
> using sequence_barrier =
basic_sequence_barrier<
    Value,
    Comparer,
    select_continuation_type<Policies..., default_continuation_type>
>;

template<
    typename Value,
    typename Comparer,
    typename Continuation
> class basic_sequence_barrier
    :
    private immovable_object
{
    using value_type = Value;
    using atomic_value_type = std::atomic<value_type>;

    class awaiter;
    struct awaiter_heap_builder;

    atomic_value_type m_publishedValue;
    std::atomic<awaiter*> m_queuedAwaiters;
    std::atomic<awaiter*> m_awaitersHeap;
    awaiter_heap_builder m_heapBuilder;

    static constexpr size_t maximumAwaiterDegree = std::numeric_limits<size_t>::digits;
    typedef size_t degree_type;

    class awaiter
    {
        template<
            typename Value,
            typename Less,
            typename Continuation
        > friend class basic_sequence_barrier;

        value_type m_value;

        basic_sequence_barrier* m_sequenceBarrier;
        awaiter* m_siblingPointer;
        awaiter* m_subtreePointer = nullptr;
        degree_type m_degree = 0;
        Continuation m_continuation;

        awaiter(
            basic_sequence_barrier* sequenceBarrier,
            value_type value
        ) :
            m_sequenceBarrier{ sequenceBarrier },
            m_value{ value }
        {}

    public:
        bool await_ready() noexcept
        {
            auto publishedValue = m_sequenceBarrier->m_publishedValue.load(
                std::memory_order_acquire
            );

            if (!m_sequenceBarrier->m_heapBuilder.m_comparer(
                publishedValue,
                m_value
            ))
            {
                m_value = publishedValue;
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
            auto nextQueuedAwaiter = m_sequenceBarrier->basic_sequence_barrier::m_queuedAwaiters.load(
                std::memory_order_relaxed
            );

            do
            {
                m_siblingPointer = nextQueuedAwaiter;
            } while (!m_sequenceBarrier->basic_sequence_barrier::m_queuedAwaiters.compare_exchange_weak(
                nextQueuedAwaiter,
                this,
                std::memory_order_release,
                std::memory_order_relaxed
            ));

            // Double check to see if the value has been published.
            auto publishedValue = m_sequenceBarrier->basic_sequence_barrier::m_publishedValue.load(
                std::memory_order_acquire
            );

            if (!m_sequenceBarrier->basic_sequence_barrier::m_heapBuilder.m_comparer(
                publishedValue,
                m_value))
            {
                m_value = publishedValue;

                // Try to resume awaiters,
                // and if we in particular desire to resume this object,
                // do not suspend.
                bool resumeThisAwaiter = false;

                m_sequenceBarrier->basic_sequence_barrier::resume_awaiters(
                    m_value,
                    this,
                    resumeThisAwaiter
                );

                return resumeThisAwaiter;
            }

            return true;
        }

        value_type await_resume() noexcept
        {
            return m_value;
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
                left->m_value,
                right->m_value);
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
        value_type& publishedValue,
        awaiter* specialAwaiter,
        bool& resumeSpecialAwaiter
    )
    {
        resumeSpecialAwaiter = false;
        awaiter* awaitersToResume = nullptr;

        // Take ownership of the enqueued awaiters.
        // We only need to do this once, since any new queued awaiter after this step
        // that would need to be resumed will itself do this sequence on its thread.
        awaiter* newAwaitersHeap = self.basic_sequence_barrier::m_queuedAwaiters.exchange(
            nullptr,
            std::memory_order_acquire
        );

        while (true)
        {
            auto previousPublishedValue = publishedValue;

            // Take ownership of the awaiters heap
            auto oldAwaitersHeap = self.basic_sequence_barrier::m_awaitersHeap.exchange(
                nullptr,
                std::memory_order_acquire
            );

            auto predicate = self.basic_sequence_barrier::m_heapBuilder.collect_predicate(
                &awaitersToResume,
                [&](awaiter* heap)
                {
                    return !self.basic_sequence_barrier::m_heapBuilder.m_comparer(
                        heap->m_value,
                        publishedValue
                    );
                });

            auto heapsToExtract = {
                oldAwaitersHeap,
                newAwaitersHeap
            };

            newAwaitersHeap = self.basic_sequence_barrier::m_heapBuilder.extract(
                std::move(predicate),
                std::move(heapsToExtract));

            // Put back the heap if we can
            oldAwaitersHeap = nullptr;
            if (newAwaitersHeap != nullptr
                &&
                !self.basic_sequence_barrier::m_awaitersHeap.compare_exchange_strong(
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
            publishedValue = self.basic_sequence_barrier::m_publishedValue.load(
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
            if (publishedValue == previousPublishedValue)
            {
                break;
            }
        }

    }

public:
    explicit basic_sequence_barrier(
        value_type initialPublishedValue = 0,
        Comparer comparer = {}
    ) noexcept :
        m_publishedValue { initialPublishedValue },
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
        self.basic_sequence_barrier::m_publishedValue.store(
            value,
            std::memory_order_release
        );

        bool resumeSpecialAwaiter;

        self.basic_sequence_barrier::resume_awaiters(
            value,
            nullptr,
            resumeSpecialAwaiter
        );
    }

    awaiter wait_until_published(
        this auto& self,
        value_type value
    ) noexcept
    {
        return awaiter{ &self, value };
    }

    auto last_published() const noexcept
    {
        return m_publishedValue.load(
            std::memory_order_acquire);
    }
};
}

using detail::sequence_barrier;
}
