#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_CANCELLATION_TOKEN_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_CANCELLATION_TOKEN_HPP

#include <stop_token>
#include "operation_cancelled.hpp"

namespace cppcoro
{

class cancellation_source;

class cancellation_token
{
    friend class cancellation_source;

    std::stop_token m_token;

public:
    cancellation_token(
        std::stop_token token
    ) : m_token{ std::move(token) }
    {}

    bool can_be_cancelled() const noexcept
    {
        return m_token.stop_possible();
    }

    bool is_cancellation_requested() const noexcept
    {
        return m_token.stop_requested();
    }

    void throw_if_cancellation_requested() const
    {
        if (is_cancellation_requested())
        {
            throw operation_cancelled();
        }
    }
};

}
#endif
