#ifndef PHANTOM_COROUTINES_INCLUDE_CONSECUTIVE_GLOBAL_ID_H
#define PHANTOM_COROUTINES_INCLUDE_CONSECUTIVE_GLOBAL_ID_H

#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <cstddef>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value = std::size_t
>
class consecutive_global_id
{
    static std::atomic<Value>& global_value()
    {
        static std::atomic<Value> globalValue;
        return globalValue;
    }
    Value m_value;

public:
    consecutive_global_id()
        :
        m_value(
            global_value().fetch_add(1)
        )
    {
    }

    Value get() const
    {
        return m_value;
    }

    operator Value() const
    {
        return get();
    }

    Value operator*() const
    {
        return get();
    }

    const Value* operator->() const
    {
        return &m_value;
    }
};

}
}
#endif
