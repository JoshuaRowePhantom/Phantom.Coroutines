#ifndef PHANTOM_COROUTINES_INCLUDE_STATIC_THREAD_POOL_H
#define PHANTOM_COROUTINES_INCLUDE_STATIC_THREAD_POOL_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <latch>
#include <thread>
#include <vector>
#include "detail/config.h"
#include "scheduler.h"
#include "thread_pool_scheduler.h"
#endif

#include "detail/assert_is_configured_module.h"

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
    size_t m_threadCount;

public:
    explicit static_thread_pool(
        size_t threadCount = std::thread::hardware_concurrency()
    ) : 
        m_threadCount(threadCount),
        m_stopLatch(threadCount)
    {
        for (size_t threadCounter = 0; threadCounter < threadCount; threadCounter++)
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
        return m_threadCount;
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

PHANTOM_COROUTINES_MODULE_EXPORT
using Phantom::Coroutines::detail::static_thread_pool;
}
#endif
