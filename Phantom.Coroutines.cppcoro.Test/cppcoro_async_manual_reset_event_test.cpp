#include "cppcoro/async_manual_reset_event.hpp"

static_assert(std::same_as<
    cppcoro::async_manual_reset_event, 
    Phantom::Coroutines::async_manual_reset_event<
        Phantom::Coroutines::multiple_awaiters,
        Phantom::Coroutines::noop_on_destroy,
        Phantom::Coroutines::default_continuation_type,
        Phantom::Coroutines::await_is_not_cancellable
    >>);
