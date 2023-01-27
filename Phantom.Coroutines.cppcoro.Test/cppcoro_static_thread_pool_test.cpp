#include "cppcoro/static_thread_pool.hpp"

static_assert(
    std::same_as<
    ::Phantom::Coroutines::static_thread_pool<>,
    ::cppcoro::static_thread_pool
    >);
