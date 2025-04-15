#ifndef PHANTOM_COROUTINES_INCLUDE_ASYNC_LATCH_H
#define PHANTOM_COROUTINES_INCLUDE_ASYNC_LATCH_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <cstddef>
#include "async_manual_reset_event.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
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
#endif
