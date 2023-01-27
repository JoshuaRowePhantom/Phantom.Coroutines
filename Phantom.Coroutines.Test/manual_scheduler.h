#include "Phantom.Coroutines/async_auto_reset_event.h"

namespace Phantom::Coroutines::detail
{

class manual_scheduler
{
    async_auto_reset_event<> m_event;
    std::atomic<size_t> m_events;

public:
    auto& schedule() noexcept
    {
        m_events.fetch_add(1, std::memory_order_relaxed);
        return m_event;
    }

    void release() noexcept
    {
        m_event.set();
    }

    auto events() const noexcept
    {
        return m_events.load(std::memory_order_acquire);
    }
};

}
