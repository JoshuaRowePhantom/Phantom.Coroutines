#include "cppcoro/task.hpp"

static_assert(std::same_as<cppcoro::task<>, Phantom::Coroutines::task<>>);
