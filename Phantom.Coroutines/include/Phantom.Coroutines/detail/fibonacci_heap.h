#pragma once

#include <array>
#include <initializer_list>
#include <limits>

namespace Phantom::Coroutines
{
namespace detail
{

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
                auto next = self.sibling(heap);
                auto child = *self.child(heap);
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

};

}
}
