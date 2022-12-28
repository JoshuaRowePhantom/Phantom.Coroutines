#pragma once
#include <concepts>
#include <optional>

namespace Phantom::Coroutines
{

template<
    typename ThreadLocalContext
> concept is_thread_local_context = requires (typename ThreadLocalContext::value_type value)
{
    typename ThreadLocalContext::value_type;
    { ThreadLocalContext::current() = value };
    { ThreadLocalContext::current() } -> std::convertible_to<typename ThreadLocalContext::value_type>;
};

template<
    typename Value
> class thread_local_context
{
public:
    typedef Value value_type;

private:
    static inline thread_local Value m_value;

public:
    static value_type& current()
    {
        return m_value;
    }
};

template<
    is_thread_local_context ThreadLocalContext
> class thread_local_context_scope
{
public:
    typedef ThreadLocalContext context_type;
    typedef typename context_type::value_type value_type;

private:
    value_type m_previousValue;

public:
    // Prevent all copying and moving.
    auto operator=(
        thread_local_context_scope&&
    ) = delete;

    template<
        typename Value
    >
    thread_local_context_scope(
        Value&& value
    ) :
        m_previousValue
    {
            std::move(ThreadLocalContext::current())
    }
    {
        ThreadLocalContext::current() = std::move(value);
    }

    ~thread_local_context_scope()
    {
        ThreadLocalContext::current() = std::move(m_previousValue);
    }
};

}