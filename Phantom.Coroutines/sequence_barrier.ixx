#pragma once

import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.fibonacci_heap;
import Phantom.Coroutines.immovable_object;
import <atomic>;
import <concepts>;
import <limits>;

namespace Phantom::Coroutines
{
template<
	typename Traits
> concept SequenceBarrierTraits = requires (
	typename Traits::value_type value
	)
{
	typename Traits::value_type;
	typename Traits::atomic_value_type;
	{ Traits::precedes(value, value) } -> std::convertible_to<bool>;
};

template<
	typename Value
>
struct sequence_barrier_traits
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
	typename Value = size_t,
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
	typedef size_t degree_type;

	class awaiter
	{
		template<
			typename Value,
			SequenceBarrierTraits Traits
		> friend class sequence_barrier;

		value_type m_value;

		sequence_barrier* m_sequenceBarrier;
		awaiter* m_siblingPointer;
		awaiter* m_subtreePointer = nullptr;
		degree_type m_degree = 0;
		coroutine_handle<> m_continuation;

		awaiter(
			sequence_barrier* sequenceBarrier,
			value_type value
		) : 
			m_sequenceBarrier { sequenceBarrier },
			m_value { value }
		{}

	public:
		bool await_ready() noexcept
		{
			auto publishedValue = m_sequenceBarrier->m_publishedValue.load(
				std::memory_order_acquire
			);

			if (!Traits::precedes(
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
			coroutine_handle<> continuation
		) noexcept
		{
			m_continuation = continuation;

			// Enqueue this awaiter into the linked list of awaiters.
			auto nextQueuedAwaiter = m_sequenceBarrier->m_queuedAwaiters.load(
				std::memory_order_relaxed
			);

			do
			{
				m_siblingPointer = nextQueuedAwaiter;
			}
			while (!m_sequenceBarrier->m_queuedAwaiters.compare_exchange_weak(
				nextQueuedAwaiter,
				this,
				std::memory_order_release,
				std::memory_order_relaxed
			));

			// Double check to see if the value has been published.
			auto publishedValue = m_sequenceBarrier->m_publishedValue.load(
				std::memory_order_acquire
			);

			if (!Traits::precedes(
				publishedValue,
				m_value))
			{
				m_value = publishedValue;

				// Try to resume awaiters,
				// and if we in particular desire to resume this object,
				// do not suspend.
				bool resumeThisAwaiter = false;

				m_sequenceBarrier->resume_awaiters(
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

	struct awaiter_heap_traits
	{
		typedef awaiter* heap_type;

		static bool precedes(
			awaiter* left,
			awaiter* right
		) {
			return Traits::precedes(
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

	static_assert(FibonacciHeapTraits<awaiter_heap_traits>);

	void resume_awaiters(
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
		awaiter* newAwaitersHeap = m_queuedAwaiters.exchange(
			nullptr,
			std::memory_order_acquire
		);

		while (true)
		{
			auto previousPublishedValue = publishedValue;

			// Take ownership of the awaiters heap
			auto oldAwaitersHeap = m_awaitersHeap.exchange(
				nullptr,
				std::memory_order_acquire
			);

			auto predicate = fibonacci_heap_collect_predicate<awaiter_heap_traits>(
				&awaitersToResume,
				[&](awaiter* heap)
				{
					return !Traits::precedes(
						heap->m_value,
						publishedValue
					);
				});

			auto heapsToExtract = {
				oldAwaitersHeap,
				newAwaitersHeap
			};

			newAwaitersHeap = fibonacci_heap_extract<
				awaiter_heap_traits, 
				std::initializer_list<awaiter_heap_traits::heap_type>>(
					std::move(predicate),
					std::move(heapsToExtract)
				);

			// Put back the heap if we can
			oldAwaitersHeap = nullptr;
			if (newAwaitersHeap != nullptr
				&&
				!m_awaitersHeap.compare_exchange_strong(
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
			if (publishedValue == previousPublishedValue)
			{
				break;
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

		bool resumeSpecialAwaiter;

		resume_awaiters(
			value,
			nullptr,
			resumeSpecialAwaiter
		);
	}

	awaiter wait_until_published(
		value_type value
	)
	{
		return awaiter{ this, value };
	}
};

}
}