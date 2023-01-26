#include "cppcoro/sequence_barrier.hpp"

static_assert(std::same_as<
    ::Phantom::Coroutines::sequence_barrier<size_t>,
    ::cppcoro::sequence_barrier<size_t>
    >);
