#include <thread>
#include <vector>
#include "scheduler.h"
#include "thread_pool_scheduler.h"
#include <latch>

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename ThreadPoolScheduler = thread_pool_scheduler<>
>
class static_thread_pool
{
    ThreadPoolScheduler m_scheduler;
    std::stop_source m_stopSource;
    std::latch m_stopLatch;

public:
    explicit static_thread_pool(
        std::size_t threadCount = std::thread::hardware_concurrency()
    ) : 
        m_stopLatch(threadCount)
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

    auto thread_count() const noexcept
    {
        return m_stopLatch.max();
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

}

using Phantom::Coroutines::detail::static_thread_pool;
}