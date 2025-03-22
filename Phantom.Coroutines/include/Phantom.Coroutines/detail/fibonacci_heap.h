#ifndef PHANTOM_COROUTINES_INCLUDE_FIBONACCI_HEAP_H
#define PHANTOM_COROUTINES_INCLUDE_FIBONACCI_HEAP_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <array>
#include <initializer_list>
#include <limits>
#include "config.h"
#endif

#include "assert_is_configured_module.h"

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Builder
> concept is_fibonacci_heap_builder = requires(
    std::decay_t<Builder> builder,
    typename std::decay_t<Builder>::heap_type node,
    size_t degree)
{
    { builder.precedes(node, node) } -> std::convertible_to<bool>;
    { builder.is_empty(node) } -> std::convertible_to<bool>;
    { builder.empty() } -> std::convertible_to<typename std::decay_t<Builder>::heap_type>;
    { builder.child(node) } -> std::convertible_to<typename std::decay_t<Builder>::heap_type*>;
    { builder.sibling(node) } -> std::convertible_to<typename std::decay_t<Builder>::heap_type*>;
    builder.degree(node) = degree;
    { builder.degree(node) } -> std::convertible_to<size_t>;
    std::swap(node, node);
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename HeapType
> class fibonacci_heap_builder
{
public:
    using heap_type = HeapType;

private:
    static constexpr size_t fibonacci_heap_maximum_degree = std::numeric_limits<size_t>::digits;

    using fibonacci_heap_buffer = std::array<
        heap_type,
        fibonacci_heap_maximum_degree
    >;

    void extract_impl(
        this auto& self,
        fibonacci_heap_buffer& buffer,
        std::predicate<heap_type> auto&& predicate,
        std::ranges::range auto&& heaps
    )
    {
        for (auto heap : heaps)
        {
            while (heap)
            {
                auto child = *self.child(heap);
                auto nextHeap = *self.sibling(heap);

                if (predicate(heap))
                {
                    // If the item matches, then we remove this item from
                    // the heap by not copying it.
                    // We then process the children.
                    // The children that match will also get removed by
                    // not being copied to the new heap;
                    // the children that do not match will get copied to the new
                    // heap in the "else" clause below.
                    self.extract_impl(
                        buffer,
                        std::forward<decltype(predicate)>(predicate),
                        std::array
                        {
                            child
                        }
                    );
                }
                else
                {
                    // Otherwise we buffer this heap item,
                    // joining together heaps of the same degree.
                    do
                    {
                        auto degree = self.degree(heap);
                        auto otherHeap = buffer[degree];
                        if (self.is_empty(otherHeap))
                        {
                            break;
                        }
                        buffer[degree] = self.empty();

                        if (self.precedes(otherHeap, heap))
                        {
                            std::swap(otherHeap, heap);
                        }
                        
                        self.degree(heap) = degree + 1;
                        *self.sibling(otherHeap) = *self.child(heap);
                        *self.child(heap) = otherHeap;
                    } while (true);

                    buffer[self.degree(heap)] = heap;
                }

                heap = nextHeap;
            }
        }
    }

    bool is_canonical_head(
        this auto& self,
        const heap_type& heap
    )
    {
        // A canonical fibonacci heap head should have 1 child of each degree smaller than itself.
        // Start with all degrees present >= than the degree of the heap.
        size_t degreesPresent = std::numeric_limits<size_t>::max() & ~((1 << (self.degree(heap))) - 1);

        // We iterate through the list using two pointers, one that moves at twice the speed of the other,
        // in order to detect cycles in the list.
        heap_type slowerChild = *self.child(heap);
        bool incrementSlowerChild = false;

        heap_type child = *self.child(heap);
        while (child)
        {
            if (self.degree(child) >= self.degree(heap))
            {
                return false;
            }

            size_t childDegreeMask = 1ULL << self.degree(child);
            if (degreesPresent & childDegreeMask)
            {
                return false;
            }

            if (self.precedes(child, heap))
            {
                return false;
            }

            if (!self.is_canonical_head(child))
            {
                return false;
            }

            degreesPresent |= childDegreeMask;

            child = *self.sibling(child);
            if (incrementSlowerChild)
            {
                slowerChild = *self.sibling(slowerChild);
            }
            incrementSlowerChild = !incrementSlowerChild;

            if (slowerChild == child)
            {
                // There is a cycle.
                return false;
            }
        }

        if (degreesPresent != std::numeric_limits<size_t>::max())
        {
            return false;
        }

        return true;
    }

public:
    heap_type extract(
        this auto& self,
        std::predicate<heap_type> auto&& predicate,
        std::ranges::range auto&& heaps
    )
    {
        static_assert(is_fibonacci_heap_builder<decltype(self)>);

        fibonacci_heap_buffer buffer;
        for (auto& bufferItem : buffer)
        {
            bufferItem = self.empty();
        }

        self.extract_impl(
            buffer,
            std::forward<decltype(predicate)>(predicate),
            std::forward<decltype(heaps)>(heaps)
            );

        auto newHeap = self.empty();

        for (auto& bufferItem : buffer)
        {
            if (!self.is_empty(bufferItem))
            {
                *self.sibling(bufferItem) = newHeap;
                newHeap = bufferItem;
            }
        }

        return newHeap;
    }

    auto collect_predicate(
        this auto& self,
        auto* matchingItems,
        auto&& predicate
    )
    {
        static_assert(is_fibonacci_heap_builder<decltype(self)>);

        return[
            &self,
            matchingItems,
            predicate = std::forward<decltype(predicate)>(predicate)
        ](
            auto node
            )
        {
            if (predicate(node))
            {
                self.degree(node) = 0;
                *self.sibling(node) = *matchingItems;
                *self.child(node) = nullptr;
                *matchingItems = node;
                return true;
            }
            return false;
        };
    }

    bool is_canonical(
        this auto& self,
        const heap_type& heap
    )
    {
        size_t degreesPresent = 0;
        // There should be no duplicate roots of the same degree,
        // each root should be a canonical heap.
        // Checking for duplicate nodes of a given degree implicitly
        // does cycle checking in the list.
        for (heap_type root = heap;
            root;
            root = *self.sibling(root))
        {
            if (!self.is_canonical_head(root))
            {
                return false;
            }

            size_t degreeMask = 1ULL << self.degree(root);
            if (degreesPresent & degreeMask)
            {
                return false;
            }

            degreesPresent |= degreeMask;
        }

        return true;
    }

};

}
}
#endif
