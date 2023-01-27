#include "../Phantom.Coroutines.Test/async_test.h"
#include "../Phantom.Coroutines.Test/manual_scheduler.h"
#include "cppcoro/async_scope.hpp"
#include "cppcoro/sequence_barrier.hpp"
#include "cppcoro/task.hpp"

namespace cppcoro
{
static_assert(!std::is_copy_constructible_v<sequence_barrier<size_t>>);

ASYNC_TEST(cppcoro_sequence_barrier_test, wait_until_published_resumes_on_scheduler)
{
    ::Phantom::Coroutines::detail::manual_scheduler scheduler;
    sequence_barrier<size_t> barrier;

    bool reached5 = false;
    bool reached7 = false;

    auto lambda = [&]() -> task<>
    {
        co_await barrier.wait_until_published(5, scheduler);
        reached5 = true;
        co_await barrier.wait_until_published(7, scheduler);
        reached7 = true;
    };
    async_scope scope;
    scope.spawn(lambda());

    barrier.publish(4);
    EXPECT_EQ(0, scheduler.events());
    EXPECT_EQ(false, reached5);
    barrier.publish(5);
    EXPECT_EQ(1, scheduler.events());
    EXPECT_EQ(false, reached5);
    scheduler.release();
    EXPECT_EQ(true, reached5);
    barrier.publish(6);
    EXPECT_EQ(1, scheduler.events());
    EXPECT_EQ(false, reached7);
    barrier.publish(7);
    EXPECT_EQ(2, scheduler.events());
    EXPECT_EQ(false, reached7);
    scheduler.release();
    EXPECT_EQ(true, reached7);

    co_await scope.join();
}

}