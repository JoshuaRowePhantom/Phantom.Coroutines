#pragma once
#include "aligned_array.h"
#include <algorithm>
#include <ranges>

namespace Phantom::Coroutines
{

// Default implementation of get_current_shard() that returns t.get_current_shard()
decltype(auto) get_current_shard(
    auto& t
)
    requires requires
{
    t.get_current_shard();
}
{
    return t.get_current_shard();
}

// Default implementation of get_shards() that returns t.get_shards()
decltype(auto) get_shards(
    auto& t
)
    requires requires
{
    t.get_shards();
}
{
    return t.get_shards();
}

// Default implementation of get_shard_count() that returns t.get_shard_count()
decltype(auto) get_shard_count(
    auto& t
)
    requires requires
{
    { t.get_shard_count() } -> std::convertible_to<size_t>;
}
{
    return t.get_shard_count();
}

decltype(auto) get_current_shard_number(
    auto& t
)
    requires requires
{
    { t.get_current_shard_number() } -> std::convertible_to<size_t>;
}
{
    return t.get_current_shard_number();
}

template<
    typename I,
    typename T,
    typename...Args
>
decltype(auto) create_shards(
    T& t,
    Args&&... args
)
{
    return t.create_shards<I>(
        std::forward<Args>(args)...);
}

template<
    typename I,
    typename T,
    typename...Args
>
decltype(auto) create_cache_aligned_shards(
    T& t,
    Args&&... args
)
{
    return t.create_cache_aligned_shards<I>(
        std::forward<Args>(args)...);
}

template<
    typename T
> concept is_shard_numbering = requires(T t)
{
    { get_current_shard_number(t) } -> std::convertible_to<size_t>;
    { get_shard_count(t) } -> std::convertible_to<size_t>;
};

template<
    typename T,
    typename I
> concept is_shard_factory = requires(T t)
{
    { create_shards<I>(t) };
    { create_cache_aligned_shards<I>(t) };
};

// A sharded item supports get_shard(T) and get_shards(T) (which supports iteration)
template<
    typename T
> concept is_sharded = is_shard_numbering<T> && requires (
    T t,
    size_t index)
{
    { get_current_shard(t) };
    { get_shards(t).size() } -> std::convertible_to<size_t>;
    { get_shards(t).begin() };
    { get_shards(t).end() };
    { get_shards(t)[index] };
};

template<
    size_t Shards
>
struct static_shard_numbering
{
    static constexpr size_t shard_count = Shards;

    static constexpr size_t get_shard_count()
    {
        return shard_count;
    }

    template<
        typename I,
        typename ItemConstructor = = decltype([](auto) { return I{}; })
    >
    static constexpr std::array<I, Shards> create_shards(
        ItemConstructor && itemConstructor = {})
    {
        auto builder = [&]<size_t ... Indices>(std::index_sequence<Indices...>)->std::array<I, Shards>
        {
            return { { itemConstructor(Indices)... } };
        };

        return builder(std::index_sequence<shard_count>{});
    }
    
    template<
        typename I,
        typename ItemConstructor = decltype([](auto) { return I{}; })
    >
    static constexpr cache_aligned_array<I, Shards> create_cache_aligned_shards(
        ItemConstructor&& itemConstructor = {})
    {
        auto builder = [&]<size_t ... Indices>(std::index_sequence<Indices...>) -> cache_aligned_array<I, Shards>
        {
            return { { itemConstructor(Indices)... } };
        };

        return builder(std::index_sequence<shard_count>{});
    }
};

template<
    size_t Shards
>
struct static_thread_id_shard_numbering
    :
    static_shard_numbering<Shards>
{
    using static_shard_numbering<Shards>::get_shard_count;
    using static_shard_numbering<Shards>::create_shards;
    using static_shard_numbering<Shards>::create_cache_aligned_shards;

    static inline std::atomic<size_t> next_thread_index = 0;
    static inline thread_local size_t current_thread_index = ++next_thread_index % Shards;

    static size_t get_current_shard_number()
    {
        return current_thread_index;
    }
};

template<
    typename Range,
    is_shard_numbering ShardNumbering
>
struct sharded_range
{
    Range shards;
    ShardNumbering shardNumbering;

    auto get_current_shard_number()
    {
        // Use ADL to lookup get_current_shard_number
        using Phantom::Coroutines::get_current_shard_number;
        return get_current_shard_number(shardNumbering);
    }

    auto get_shard_count()
    {
        // Use ADL to lookup get_shard_count
        using Phantom::Coroutines::get_shard_count;
        return get_shard_count(shardNumbering);
    }

    auto& get_current_shard()
    {
        return shards[get_current_shard_number()];
    }

    auto& get_shards()
    {
        return shards;
    }
};

template<
    typename T,
    is_shard_numbering ShardNumbering
> 
using cache_aligned_sharded_range =
    sharded_range<
        decltype(create_cache_aligned_shards<T>(std::declval<ShardNumbering&>())),
        ShardNumbering
    >;

template<
    typename T,
    size_t Shards = 32
>
using static_cache_aligned_sharded_array = cache_aligned_sharded_range<
    T,
    static_thread_id_shard_numbering<Shards>
>;

template<
    is_sharded Sharded,
    typename Transformation
>
struct transformed_sharded_range
{
    Sharded sharded;
    Transformation transformation;

    using shards_type = decltype(std::ranges::transform(get_shards(sharded), transformation));
    shards_type shards = std::ranges::transform(get_shards(sharded), transformation);

    decltype(auto) get_current_shard()
    {
        return transformation(
            get_current_shard(sharded)
        );
    }

    auto& get_shards()
    {
        return shards;
    }
};

}
