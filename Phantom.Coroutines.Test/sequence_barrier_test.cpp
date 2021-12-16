#include "async_test.h"
#include "Phantom.Coroutines/sequence_barrier.h"
#include "Phantom.Coroutines/suspend_result.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(std::same_as<std::size_t, awaitable_result_type_t<decltype(std::declval<sequence_barrier<>>().wait_for(0))>>);
static_assert(is_awaiter<decltype(std::declval<sequence_barrier<>>().wait_for(0))>);

ASYNC_TEST(sequence_barrier_test, Can_await_barrier_at_zero)
{
	suspend_result suspendResult;
	sequence_barrier<> sequenceBarrier;
	co_await (suspendResult << sequenceBarrier.wait_for(0));
}