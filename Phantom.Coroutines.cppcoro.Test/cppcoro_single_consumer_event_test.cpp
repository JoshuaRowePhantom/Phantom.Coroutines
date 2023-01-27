#include "cppcoro/single_consumer_event.hpp"

static_assert(std::same_as<
    ::cppcoro::single_consumer_event,
    ::Phantom::Coroutines::async_manual_reset_event<
        ::Phantom::Coroutines::single_awaiter
    >>);
