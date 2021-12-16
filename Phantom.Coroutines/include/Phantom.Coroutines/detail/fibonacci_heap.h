#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#include <limits>

namespace Phantom::Coroutines
{
namespace detail
{
template<
	typename Traits
> concept FibonacciHeapTraits = requires(
	typename Traits::heap_type heap,
	size_t degree)
{
	typename Traits::heap_type;
	{ Traits::precedes(heap, heap) } -> std::convertible_to<bool>;
	{ Traits::is_empty(heap) } -> std::convertible_to<bool>;
	{ Traits::empty() } -> std::convertible_to<typename Traits::heap_type>;
	{ Traits::child(heap) } -> std::convertible_to<typename Traits::heap_type*>;
	{ Traits::sibling(heap) } -> std::convertible_to<typename Traits::heap_type*>;
	Traits::degree(heap) = degree;
	{ Traits::degree(heap) } -> std::convertible_to<size_t>;
	std::swap(heap, heap);
};

// Appends one fibonacci heap to another cheaply in O(1) time.
template<
	FibonacciHeapTraits Traits
> void fibonacci_heap_append(
	typename Traits::heap_type* heap1,
	typename Traits::heap_type heap2
)
{
	Traits::link(heap1, heap2);
}

static constexpr size_t fibonacci_heap_maximum_degree = std::numeric_limits<size_t>::digits;

template<
	typename Traits
> using fibonacci_heap_buffer = std::array<
	typename Traits::heap_type,
	fibonacci_heap_maximum_degree
>;

template<
	FibonacciHeapTraits Traits,
	std::predicate<typename Traits::heap_type> Predicate,
	std::ranges::range<typename Traits::heap_type> Range
> void fibonacci_heap_extract_impl(
	fibonacci_heap_buffer<Traits>& buffer,
	Predicate& predicate,
	Range&& heaps
)
{
	for (auto heap : heaps)
	{
		while (heap)
		{
			auto next = Traits::sibling(heap);
			auto child = *Traits::child(heap);
			auto nextHeap = *next;

			if (predicate(heap))
			{
				// If the item matches, then we remove this item from
				// the heap by not copying it.
				// We then process the children.
				// The children that match will also get removed by
				// not being copied to the new heap;
				// the children that do not match will get copied to the new
				// heap in the "else" clause below.
				fibonacci_heap_extract(
					buffer,
					&child,
					predicate
				);
			}
			else
			{
				// Otherwise we buffer this heap item,
				// joining together heaps of the same degree.
				do
				{
					auto degree = Traits::degree(heap);
					auto otherHeap = buffer[degree];
					if (Traits::is_empty(otherHeap))
					{
						break;
					}
					buffer[degree] = Traits::empty();

					if (Traits::precedes(otherHeap, heap))
					{
						std::swap(otherHeap, heap);
					}

					Traits::degree(heap) = degree + 1;
					*Traits::sibling(otherHeap) = *Traits::child(heap);
					*Traits::child(heap) = otherHeap;
				} while (true);

				buffer[Traits::degree(heap)] = heap;
			}

			heap = nextHeap;
		}
	}
}

// Process each heap item with the predicate, not guaranteeing
// evaluation of the predicate for a given item if the predicate did not return true
// for all items preceding that item.
// 
// The passed in heap is modified to not contain the items for which
// the predicate returned true.  
//
// The predicate is passed the head of the heap to test;
// if the predicate returns true, each child of the predicate
// is then passed to the predicate.  If the predicate returns
// false, then the children are not processed.  Thus,
// the typical usage is to process all heap items below
// some threshold value.
//
// The predicate is allowed to modify the result of child() and sibling()
// before returning; these values are cached before calling the predicate.
// 
// The resulting heap is canonical, such that a future fibonacci_heap_extract
// on it will return in O(log n) time.
template<
	FibonacciHeapTraits Traits,
	std::predicate<typename Traits::heap_type> Predicate,
	std::ranges::range<typename Traits::heap_type> Range
> typename Traits::heap_type fibonacci_heap_extract(
	Predicate predicate,
	Range&& heaps
	)
{
	fibonacci_heap_buffer<Traits> buffer;
	for (auto& bufferItem : buffer)
	{
		bufferItem = Traits::empty();
	}

	fibonacci_heap_extract_impl(
		buffer,
		predicate,
		std::forward<Range>(heaps)
	);

	typename Traits::heap_type newHeap = Traits::empty(newHeap);

	for (auto& bufferItem : buffer)
	{
		if (!Traits::is_empty(bufferItem))
		{
			*Traits::sibling(bufferItem) = newHeap;
			newHeap = bufferItem;
		}
	}

	return newHeap;
}

// An implementation of the fibonacci_heap_extract predicate
// that collects the matching nodes into a new non-canonical heap.
template<
	FibonacciHeapTraits Traits,
	std::predicate<typename Traits::heap_type> Predicate
> auto fibonacci_heap_collect_predicate(
	typename Traits::heap_type* matchingItems,
	Predicate&& predicate
)
{
	return [
		matchingItems,
		predicate = std::forward<Predicate>(predicate)
	] (
		typename Traits::heap_type heap
	) mutable
	{
		if (predicate(heap))
		{
			*Traits::next(heap) = *matchingItems;
			*matchingItems = heap;
			return true;
		}
		return false;
	};
}

}
}
