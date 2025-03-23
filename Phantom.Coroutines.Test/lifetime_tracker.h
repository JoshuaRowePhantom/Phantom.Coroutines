#ifndef PHANTOM_COROUTINES_INCLUDE_LIFETIME_TRACKER_H
#define PHANTOM_COROUTINES_INCLUDE_LIFETIME_TRACKER_H
#if defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/config.h"
#include <assert.h>
#include <memory>
#endif

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
class lifetime_tracker;

PHANTOM_COROUTINES_MODULE_EXPORT
class lifetime_statistics
{
public:
    size_t construction_count = 0;
    size_t copy_construction_count = 0;
    size_t move_construction_count = 0;
    size_t destruction_count = 0;
    size_t replace_count = 0;
    size_t copy_count = 0;
    size_t move_into_count = 0;
    size_t move_from_count = 0;
    size_t instance_count = 0;
    bool used_after_move = false;

    inline lifetime_tracker tracker();

    operator lifetime_tracker();
};

class lifetime_tracker
{
    friend class lifetime_statistics;
    
    lifetime_statistics * m_statistics;
    bool m_movedFrom = false;

public:
    lifetime_tracker(
        lifetime_statistics* statistics
    ) : m_statistics(
        statistics)
    {
        m_statistics->construction_count++;
        m_statistics->instance_count++;
    }

    lifetime_tracker(
        const lifetime_tracker& other
    ) : m_statistics(
        other.m_statistics)
    {
        m_statistics->construction_count++;
        m_statistics->instance_count++;
        m_statistics->copy_construction_count++;
    }

    lifetime_tracker(
        lifetime_tracker&& other
    ) : m_statistics(
        other.m_statistics)
    {
        m_statistics->construction_count++;
        m_statistics->instance_count++;
        m_statistics->move_construction_count++;
        other.m_movedFrom = true;
    }

    ~lifetime_tracker()
    {
        m_statistics->destruction_count++;
        m_statistics->instance_count--;
    }

    lifetime_tracker& operator=(
        const lifetime_tracker& other)
    {
        m_statistics->instance_count--;
        m_statistics->replace_count++;
        m_statistics = other.m_statistics;
        m_movedFrom = other.m_movedFrom;
        m_statistics->copy_count++;
        m_statistics->instance_count++;
        return *this;
    }

    lifetime_tracker& operator=(
        lifetime_tracker&& other
        ) noexcept
    {
        m_statistics->instance_count--;
        m_statistics->replace_count++;
        m_statistics->move_into_count++;
        m_statistics = other.m_statistics;
        m_movedFrom = other.m_movedFrom;
        m_statistics->move_from_count++;
        m_statistics->instance_count++;
        return *this;
    }

    bool use() const
    {
        assert(m_statistics);
        assert(!m_movedFrom);
        if (m_movedFrom)
        {
            m_statistics->used_after_move = true;
        }

        return !m_movedFrom;
    }

    bool moved_from() const
    {
        return m_movedFrom;
    }

    bool operator==(
        const lifetime_statistics& other
        ) const
    {
        return m_statistics == &other;
    }
};

inline lifetime_tracker lifetime_statistics::tracker()
{
    return lifetime_tracker(this);
}

inline lifetime_statistics::operator lifetime_tracker()
{
    return tracker();
}

}
#endif
