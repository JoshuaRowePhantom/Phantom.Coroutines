#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#include <limits>

namespace Phantom::Coroutines
{
template<
	typename Traits
> concept SequenceBarrierTraits = requires
{
	typename Traits::value_type;
	typename Traits::atomic_value_type;
};

template<
	typename Value
> struct sequence_barrier_traits
{
	typedef Value value_type;
	typedef std::atomic<Value> atomic_value_type;

	static constexpr bool precedes(
		const Value& value1,
		const Value& value2
	)
	{
		return value1 < value2;
	}
};

namespace detail
{

template<
	typename Value,
	SequenceBarrierTraits Traits = sequence_barrier_traits<Value>
> class sequence_barrier
	:
	private immovable_object
{
	using value_type = typename Traits::value_type;
	using atomic_value_type = typename Traits::atomic_value_type;

	class awaiter;

	atomic_value_type m_publishedValue;
	std::atomic<awaiter*> m_queuedAwaiters;
	std::atomic<awaiter*> m_awaitersHeap;

	static constexpr size_t maximumAwaiterDegree = std::numeric_limits<size_t>::digits;
	typedef int degree_type;

	class awaiter
	{
		template<
			typename Value,
			SequenceBarrierTraits Traits
		> friend class sequence_barrier;

		value_type m_value;

		sequence_barrier* m_sequenceBarrier;
		awaiter* m_siblingPointer;
		awaiter* m_subtreePointer;
		degree_type m_degree = 0;

		awaiter(
			sequence_barrier* sequenceBarrier,
			value_type value
		) : 
			m_sequenceBarrier { sequenceBarrier },
			m_value { value }
		{}

	public:
		bool await_ready() const noexcept
		{
			return !Traits::precedes(
				m_sequenceBarrier->m_publishedValue.load(
					std::memory_order_acquire
				),
				m_value
			);
		}

		bool await_suspend(
			coroutine_handle<> continuation
		) noexcept
		{
			// Enqueue this awaiter into the linked list of awaiters.
			auto nextQueuedAwaiter = m_sequenceBarrier->m_queuedAwaiters.load(
				std::memory_order_relaxed
			);
			while (!m_sequenceBarrier->m_queuedAwaiters.compare_exchange_weak(
				nextQueuedAwaiter,
				this,
				std::memory_order_release,
				std::memory_order_relaxed
			))
			{
			};

			// Double check to see if the value has been published.
			auto publishedValue = m_sequenceBarrier->m_publishedValue.load(
				std::memory_order_acquire
			);

			if (!Traits::precedes(
				publishedValue,
				m_value))
			{
				// Try to resume awaiters,
				// and if we in particular desire to resume this object,
				// do not suspend.
				return m_sequenceBarrier->trigger(
					publishedValue,
					this
				);
			}

			return true;
		}

		value_type await_resume() noexcept
		{
			// Another load will have already been performed with acquire semantics,
			// so load with relaxed semantics.
			return m_sequenceBarrier->m_publishedValue.load(
				std::memory_order_relaxed
			);
		}
	};

	void determine_awaiters_to_resume(
		value_type publishedValue,
		awaiter* awaitersHeap,
		awaiter** awaitersToResume,
		awaiter** newAwaitersHeap
	)
	{
		while (awaitersHeap)
		{
			auto nextAwaiter = awaitersHeap->m_siblingPointer;

			if (!Traits::precedes(
				publishedValue,
				awaitersHeap->m_value))
			{
				determine_awaiters_to_resume(
					publishedValue,
					awaitersHeap->m_subtreePointer,
					awaitersToResume,
					newAwaitersHeap
				);

				awaitersHeap->m_siblingPointer = *awaitersToResume;
				*awaitersToResume = *awaitersHeap;
			}
			else
			{
				*newAwaitersHeap = awaitersHeap;
				newAwaitersHeap = &awaitersHeap->m_siblingPointer;
			}

			awaitersHeap = nextAwaiter;
		}
	}

	void merge_awaiters_heaps(
		awaiter** mergedTarget,
		awaiter* mergeSource)
	{
		std::array<awaiter*, maximumAwaiterDegree> heapsByDegree = { nullptr };

		while (mergeSource)
		{
			auto nextMergeSource = mergeSource->m_siblingPointer;
			awaiter* mergeTarget;

			while (mergeTarget = heapsByDegree[mergeSource->degree])
			{
				if (Traits::precedes(
					mergeTarget->m_value,
					mergeSource->m_value))
				{
					std::swap(
						mergeSource,
						mergeTarget
					);
				}

				mergeTarget->m_siblingPointer = mergeSource->m_subtreePointer;
				mergeSource->m_subtreePointer = mergeTarget;
				++mergeSource.m_degree;
			}

			mergeSource = nextMergeSource;
		}

		*mergedTarget = nullptr;
		for (auto mergedTree : heapsByDegree)
		{
			mergedTree->m_siblingPointer = *mergedTarget;
			*mergedTarget = mergedTree;
		}
	}

	void resume_awaiters(
		value_type publishedValue,
		awaiter* specialAwaiter,
		bool& resumeSpecialAwaiter
	)
	{
		resumeSpecialAwaiter = false;
		awaiter* awaitersToResume = nullptr;

		// Take ownership of the enqueued awaiters.
		// We only need to do this once, since any new queued awaiter after this step
		// that would need to be resumed will itself do this sequence on its thread.
		awaiter* newAwaitersHeap = m_queuedAwaiters.exchange(
			nullptr,
			std::memory_order_acquire
		);

		determine_awaiters_to_resume(
			publishedValue,
			newAwaitersHeap,
			&awaitersToResume,
			&newAwaitersHeap);

		while (true)
		{
			auto previousPublishedValue = publishedValue;

			bool resumeSpecialAwaiter = false;

			// Take ownership of the awaiters heap
			auto oldAwaitersHeap = m_awaitersHeap.exchange(
				nullptr,
				std::memory_order_acquire
			);

			determine_awaiters_to_resume(
				publishedValue,
				oldAwaitersHeap,
				&awaitersToResume,
				&oldAwaitersHeap
			);

			merge_awaiters_heaps(
				&newAwaitersHeap,
				oldAwaitersHeap
			);

			// If we are going to put back no awaiters,
			// then this thread isn't putting back any awaiters
			// that might be resumable because the published value
			// has changed.  Therefore, don't rerun the loop.
			if (newAwaitersHeap == nullptr)
			{
				break;
			}

			// Put back the heap if we can
			oldAwaitersHeap = nullptr;
			if (!m_awaitersHeap.compare_exchange_strong(
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
			publishedValue = m_publishedValue.load(
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
			if (publishedValue != previousPublishedValue)
			{
				continue;
			}
		}

	}

public:
	sequence_barrier() {}
	sequence_barrier(
		value_type initialPublishedValue
	) :
		m_publishedValue { initialPublishedValue }
	{}

	void publish(
		value_type value
	)
	{
		m_publishedValue.store(
			value,
			std::memory_order_release
		);

		resume_awaiters(
			value,
			nullptr
		);
	}

	awaiter wait_for(
		value_type value
	)
	{
		return awaiter{ this, value };
	}
};

}
}