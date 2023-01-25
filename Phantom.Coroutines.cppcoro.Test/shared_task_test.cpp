#include "cppcoro/shared_task.hpp"

static_assert(std::same_as<cppcoro::shared_task<>, Phantom::Coroutines::shared_task<>>);
