#include "cppcoro/async_latch.hpp"

static_assert(
    std::same_as<
    ::Phantom::Coroutines::async_latch<>,
    ::cppcoro::async_latch
    >
    );
