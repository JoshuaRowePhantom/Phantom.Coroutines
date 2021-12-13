#include "Phantom.Coroutines/sequence_barrier.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(std::same_as<std::size_t, awaitable_result_type_t<decltype(std::declval<sequence_barrier<size_t>>().wait_for(0))>>);
