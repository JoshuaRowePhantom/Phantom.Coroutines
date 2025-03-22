#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_CANCELLATION_SOURCE_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_CANCELLATION_SOURCE_HPP

#include <stop_token>
#include "cancellation_token.hpp"

namespace cppcoro
{

class cancellation_token;

class cancellation_source
{
    std::stop_source m_stopSource;

public:
    bool can_be_cancelled() const noexcept
    {
        return m_stopSource.stop_possible();
    }

    cancellation_token token() const noexcept
    {
        return cancellation_token(m_stopSource.get_token());
    }

    void request_cancellation()
    {
        m_stopSource.request_stop();
    }

    bool is_cancellation_requested() const noexcept
    {
        return m_stopSource.stop_requested();
    }
};
}
#endif
