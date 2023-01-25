#include "cppcoro/inline_scheduler.hpp"

static_assert(std::same_as<cppcoro::inline_scheduler, Phantom::Coroutines::inline_scheduler>);
