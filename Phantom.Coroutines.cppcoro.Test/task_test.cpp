#include "cppcoro/task.hpp"

static_assert(std::same_as<::Phantom::Coroutines::reusable_task<>, ::cppcoro::task<>>);