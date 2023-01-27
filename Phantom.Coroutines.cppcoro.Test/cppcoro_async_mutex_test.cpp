#include "../Phantom.Coroutines.Test/async_test.h"
#include "cppcoro/async_auto_reset_event.hpp"
#include "cppcoro/async_scope.hpp"
#include "cppcoro/async_mutex.hpp"
#include "cppcoro/task.hpp"

static_assert(std::same_as<
    cppcoro::async_mutex, 
    Phantom::Coroutines::async_mutex<
        Phantom::Coroutines::multiple_awaiters,
        Phantom::Coroutines::noop_on_destroy,
        Phantom::Coroutines::default_continuation_type,
        Phantom::Coroutines::await_is_not_cancellable
    >>);

static_assert(
    std::same_as<
        std::unique_lock<
            cppcoro::async_mutex
        >,
        cppcoro::async_mutex_lock
    >
    );

static_assert(
    std::same_as<
    ::Phantom::Coroutines::async_mutex<>::lock_operation,
    ::cppcoro::async_mutex_lock_operation
    >);

static_assert(
    std::same_as<
    ::Phantom::Coroutines::async_mutex<>::scoped_lock_operation,
    ::cppcoro::async_mutex_scoped_lock_operation
    >);

namespace cppcoro
{
ASYNC_TEST(cppcoro_async_mutex_test, mutex_is_mutually_exclusive)
{
    async_mutex mutex;
    async_auto_reset_event event;

    bool complete1 = false;
    bool complete2 = false;

    auto lambda = [&](
        bool& complete
        ) -> task<>
    {
        auto lock = co_await mutex.scoped_lock_async();
        complete = true;
        co_await event;
    };

    async_scope scope;
    scope.spawn(lambda(complete1));
    scope.spawn(lambda(complete2));

    EXPECT_TRUE(complete1);
    EXPECT_FALSE(complete2);
    event.set();
    EXPECT_TRUE(complete2);
    event.set();

    co_await scope.join();
}
}