#include "cppcoro/async_mutex.hpp"

static_assert(std::same_as<
	cppcoro::async_mutex, 
	Phantom::Coroutines::async_mutex<
		Phantom::Coroutines::multiple_awaiters,
		Phantom::Coroutines::noop_on_destroy,
		Phantom::Coroutines::default_continuation_type,
		Phantom::Coroutines::await_is_not_cancellable
	>>);
