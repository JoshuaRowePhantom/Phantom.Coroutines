#include <assert.h>
#include <memory>

namespace Phantom::Coroutines::detail
{

class lifetime_tracker;

class lifetime_statistics
{
public:
    size_t copy_construction_count;
    size_t move_construction_count;
    size_t destruction_count;
    size_t replace_count;
    size_t copy_count;
    size_t move_into_count;
    size_t move_from_count;
    bool used_after_move;

    lifetime_tracker tracker();
};

class lifetime_tracker
{
    friend class lifetime_statistics;
    
    lifetime_statistics * m_statistics;
    bool m_movedFrom = false;

    lifetime_tracker(
        lifetime_statistics* statistics
    ) : m_statistics(
        statistics)
    {}

public:
    lifetime_tracker(
        const lifetime_tracker& other
    ) : m_statistics(
        other.m_statistics)
    {
        m_statistics->copy_construction_count++;
    }

    lifetime_tracker(
        lifetime_tracker&& other
    ) : m_statistics(
        other.m_statistics)
    {
        m_statistics->move_construction_count++;
        other.m_movedFrom = true;
    }

    ~lifetime_tracker()
    {
        m_statistics->destruction_count++;
    }

    lifetime_tracker& operator=(
        const lifetime_tracker& other)
    {
        m_statistics->replace_count++;
        m_statistics = other.m_statistics;
        m_movedFrom = other.m_movedFrom;
        m_statistics->copy_count++;
        return *this;
    }

    lifetime_tracker& operator=(
        lifetime_tracker&& other)
    {
        m_statistics->replace_count++;
        m_statistics->move_into_count++;
        m_statistics = other.m_statistics;
        m_movedFrom = other.m_movedFrom;
        m_statistics->move_from_count++;
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
};

lifetime_tracker lifetime_statistics::tracker()
{
    return lifetime_tracker(this);
}

}