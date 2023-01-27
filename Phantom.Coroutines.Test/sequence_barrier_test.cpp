#include "async_test.h"
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/sequence_barrier.h"
#include "Phantom.Coroutines/suspend_result.h"
#include "Phantom.Coroutines/sync_wait.h"
#include <random>

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(std::same_as<std::size_t, awaitable_result_type_t<decltype(std::declval<sequence_barrier<>&>().wait_until_published(0))>>);
static_assert(is_awaiter<decltype(std::declval<sequence_barrier<>&>().wait_until_published(0))>);

ASYNC_TEST(sequence_barrier_test, Awaiting_at_nothing_published_with_default_constructor_does_suspend)
{
    suspend_result suspendResult;
    sequence_barrier<> sequenceBarrier;
    bool isCompleted = false;

    auto awaiter = [&]() -> task<>
    {
        EXPECT_EQ(0, co_await sequenceBarrier.wait_until_published(0));
        isCompleted = true;
    };
    async_scope<> scope;
    scope.spawn(awaiter());

    EXPECT_FALSE(isCompleted);
    sequenceBarrier.publish(0);
    EXPECT_TRUE(isCompleted);
    co_await scope.join();
}

ASYNC_TEST(sequence_barrier_test, last_published_returns_last_published_value)
{
    suspend_result suspendResult;
    sequence_barrier<> sequenceBarrier;
    sequenceBarrier.publish(0);
    EXPECT_EQ(0, sequenceBarrier.last_published());
    sequenceBarrier.publish(5);
    EXPECT_EQ(5, sequenceBarrier.last_published());
    co_return;
}

ASYNC_TEST(sequence_barrier_test, can_start_at_nonzero_value)
{
    suspend_result suspendResult;
    sequence_barrier<> sequenceBarrier(5);
    EXPECT_EQ(5, sequenceBarrier.last_published());
    co_return;
}

TEST(sequence_barrier_test, Publish_resumes_an_awaiter_on_the_dot)
{
    suspend_result suspendResult;
    sequence_barrier<> sequenceBarrier;
    std::optional<size_t> result;

    auto future = as_future([&]() -> task<>
        {
            result = co_await(suspendResult << sequenceBarrier.wait_until_published(1));
        }());

    EXPECT_TRUE(suspendResult.did_suspend());
    EXPECT_EQ(std::optional<size_t>{}, result);

    sequenceBarrier.publish(0);
    EXPECT_EQ(std::optional<size_t>{}, result);
    sequenceBarrier.publish(1);

    EXPECT_EQ(std::optional<size_t>{1}, result);
}

TEST(sequence_barrier_test, Publish_permits_await_without_suspending_awaiter)
{
    suspend_result suspendResult;
    sequence_barrier<> sequenceBarrier;
    std::optional<size_t> result;

    sequenceBarrier.publish(1);
    
    auto future = as_future([&]() -> task<>
        {
            result = co_await(suspendResult << sequenceBarrier.wait_until_published(1));
        }());

    EXPECT_FALSE(suspendResult.did_suspend());
    EXPECT_EQ(std::optional<size_t>{1}, result);
}

ASYNC_TEST(sequence_barrier_test, Publish_steps_through_published_items)
{
    std::multimap<size_t, bool> completedItems;
    sequence_barrier<> sequenceBarrier;
    std::mt19937 random;
    std::uniform_int<size_t> distribution(0, 100);

    async_scope<> scope;
    auto waitLambda = [&](size_t waitFor, bool& isComplete) -> task<>
    {
        co_await sequenceBarrier.wait_until_published(waitFor);
        isComplete = true;
    };
    
    for (auto counter = 0; counter < 1000; ++counter)
    {
        auto value = distribution(random);
        auto iterator = completedItems.emplace(value, false);
        scope.spawn(waitLambda(value, iterator->second));
    }

    for (auto sequenceNumber = 0; sequenceNumber <= 103; sequenceNumber += 3)
    {
        sequenceBarrier.publish(sequenceNumber);

        for (auto& completedItem : completedItems)
        {
            EXPECT_EQ(
                completedItem.first <= sequenceNumber,
                completedItem.second
            );
        }
    }

    co_await scope.join();
}