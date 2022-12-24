#include <thread>
#include <vector>
#include "scheduler.h"
#include "thread_pool_scheduler.h"
#include <latch>

namespace Phantom::Coroutines
{
namespace detail
{

class static_thread_pool
{
	thread_pool_scheduler m_scheduler;
	std::stop_source m_stopSource;
	std::latch m_stopLatch;

public:
	static_thread_pool(
		std::size_t threadCount
	) : m_stopLatch(threadCount)
	{
		for (int threadCounter = 0; threadCounter < threadCount; threadCounter++)
		{
			std::thread([&]
			{
				m_scheduler.process_items(m_stopSource.get_token());
				m_stopLatch.count_down();
			}).detach();
		}
	}

	~static_thread_pool()
	{
		m_stopSource.request_stop();
		m_stopLatch.wait();
	}

	auto schedule() noexcept
	{
		return m_scheduler.schedule();
	}
};

static_assert(is_scheduler<static_thread_pool>);

}

using Phantom::Coroutines::detail::static_thread_pool;
}