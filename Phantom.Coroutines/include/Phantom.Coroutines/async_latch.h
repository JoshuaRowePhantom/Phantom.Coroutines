#pragma once

#include "async_manual_reset_event.h"
#include "type_traits.h"

namespace Phantom::Coroutines
{

template<
    typename Event = async_manual_reset_event<>
>
class async_latch
{
    std::atomic<ptrdiff_t> m_count;
    Event m_event;

public:
    async_latch(
        ptrdiff_t initialCount
    ) : m_count { initialCount }
    {
        if (m_count <= 0)
        {
            m_event.set();
        }
    }

    void count_down(ptrdiff_t count = 1)
    {
        if (m_count.fetch_sub(count, std::memory_order_relaxed) <= count)
        {
            m_event.set();
        }
    }

    auto operator co_await() const noexcept
    {
        return get_awaiter(m_event);
    }
};

}
