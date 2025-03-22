#ifndef PHANTOM_COROUTINES_INCLUDE_CONSECUTIVE_GLOBAL_ID_H
#define PHANTOM_COROUTINES_INCLUDE_CONSECUTIVE_GLOBAL_ID_H

#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <cstddef>
#endif

#include "detail/assert_is_configured_module.h"

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
    inline static std::atomic<Value> m_globalValue;
    Value m_value;

public:
    consecutive_global_id()
        :
        m_value(
            m_globalValue.fetch_add(1)
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
