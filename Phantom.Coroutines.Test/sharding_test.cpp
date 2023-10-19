#include "async_test.h"
#include "Phantom.Coroutines/sharding.h"
#include <concepts>
#include <type_traits>

namespace Phantom::Coroutines
{

static_assert(
    std::same_as<
        cache_aligned_array<int, 16>&,
        decltype(std::declval<static_cache_aligned_sharded_array<int, 16>>().get_shards())
    >);

static_assert(
    is_sharded<static_cache_aligned_sharded_array<int, 32>>
    );

}