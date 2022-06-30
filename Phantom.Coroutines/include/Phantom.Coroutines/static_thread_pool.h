#include <thread>
#include <vector>
#include "scheduler.h"
#include "thread_pool_scheduler.h"

namespace Phantom::Coroutines
{
namespace detail
{

class static_thread_pool
{
	thread_pool_scheduler m_scheduler;
	std::vector<std::thread> m_threads;
	std::stop_source m_stopSource;

public:
	static_thread_pool(
		std::size_t threadCount
	)
	{
		m_threads.reserve(threadCount);
		for (int threadCounter = 0; threadCounter < threadCount; threadCounter++)
		{
			m_threads.emplace_back(std::thread([&]
				{
					m_scheduler.process_items(m_stopSource.get_token());
				}));
		}
	}

	void shutdown()
	{
		if (m_stopSource.request_stop())
		{
			for (auto& thread : m_threads)
			{
				thread.join();
			}
		}
	}

	~static_thread_pool()
	{
		shutdown();
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