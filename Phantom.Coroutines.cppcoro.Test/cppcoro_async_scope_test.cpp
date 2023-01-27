#include "cppcoro/async_scope.hpp"

static_assert(std::same_as<
    cppcoro::async_scope, 
    Phantom::Coroutines::async_scope<
        Phantom::Coroutines::single_awaiter,
        Phantom::Coroutines::fail_on_destroy_with_awaiters,
        Phantom::Coroutines::default_continuation_type,
        Phantom::Coroutines::await_is_not_cancellable,
        Phantom::Coroutines::fail_on_use_after_join
    >>);
