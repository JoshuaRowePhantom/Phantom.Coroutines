import Phantom.Coroutines.async_test;
import Phantom.Coroutines.sequence_barrier;
import Phantom.Coroutines.suspend_result;
import Phantom.Coroutines.sync_wait;

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(std::same_as<std::size_t, awaitable_result_type_t<decltype(std::declval<sequence_barrier<>>().wait_until_published(0))>>);
static_assert(is_awaiter<decltype(std::declval<sequence_barrier<>>().wait_until_published(0))>);

ASYNC_TEST(sequence_barrier_test, Can_await_barrier_at_zero)
{
	suspend_result suspendResult;
	sequence_barrier sequenceBarrier;
	co_await (suspendResult << sequenceBarrier.wait_until_published(0));
	EXPECT_FALSE(suspendResult.did_suspend());
}

TEST(sequence_barrier_test, Publish_resumes_an_awaiter)
{
	suspend_result suspendResult;
	sequence_barrier sequenceBarrier;
	std::optional<size_t> result;

	auto future = as_future([&]() -> task<>
		{
			result = co_await(suspendResult << sequenceBarrier.wait_until_published(1));
		}());

	EXPECT_TRUE(suspendResult.did_suspend());
	EXPECT_EQ(std::optional<size_t>{}, result);

	sequenceBarrier.publish(1);

	EXPECT_EQ(std::optional<size_t>{1}, result);
}

TEST(sequence_barrier_test, Publish_permits_await_without_suspending_awaiter)
{
	suspend_result suspendResult;
	sequence_barrier sequenceBarrier;
	std::optional<size_t> result;

	sequenceBarrier.publish(1);
	
	auto future = as_future([&]() -> task<>
		{
			result = co_await(suspendResult << sequenceBarrier.wait_until_published(1));
		}());

	EXPECT_FALSE(suspendResult.did_suspend());
	EXPECT_EQ(std::optional<size_t>{1}, result);
}
