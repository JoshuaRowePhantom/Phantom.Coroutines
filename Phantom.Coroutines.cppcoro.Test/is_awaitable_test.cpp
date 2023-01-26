#include "cppcoro/is_awaitable.hpp"
#include "cppcoro/task.hpp"

static_assert(cppcoro::is_awaitable_v<cppcoro::task<>>);
static_assert(!cppcoro::is_awaitable_v<int>);

static_assert(std::same_as<std::true_type, cppcoro::is_awaitable<cppcoro::task<>>>);
static_assert(std::same_as<std::false_type, cppcoro::is_awaitable<int>>);

