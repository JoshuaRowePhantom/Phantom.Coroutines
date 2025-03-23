#ifndef PHANTOM_COROUTINES_INCLUDE_THREAD_LOCAL_CONTEXT_H
#define PHANTOM_COROUTINES_INCLUDE_THREAD_LOCAL_CONTEXT_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <optional>
#include "detail/config.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ThreadLocalContext
> concept is_thread_local_context = requires (typename ThreadLocalContext::value_type value)
{
    typename ThreadLocalContext::value_type;
    { ThreadLocalContext::current() = value };
    { ThreadLocalContext::current() } -> std::convertible_to<typename ThreadLocalContext::value_type>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
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

PHANTOM_COROUTINES_MODULE_EXPORT
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
    explicit thread_local_context_scope(
        Value&& value
    ) :
        m_previousValue
    {
        std::move(ThreadLocalContext::current())
    }
    {
        ThreadLocalContext::current() = std::forward<Value>(value);
    }

    ~thread_local_context_scope()
    {
        ThreadLocalContext::current() = std::forward<decltype(m_previousValue)>(m_previousValue);
    }
};

}
#endif
