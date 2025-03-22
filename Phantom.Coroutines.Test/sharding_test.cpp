#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.aligned_array;
import Phantom.Coroutines.sharding;
#else
#include "Phantom.Coroutines/sharding.h"
#endif
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