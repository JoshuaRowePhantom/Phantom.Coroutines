#ifndef PHANTOM_COROUTINES_INCLUDE_REUSABLE_CONSECUTIVE_GLOBAL_ID_H
#define PHANTOM_COROUTINES_INCLUDE_REUSABLE_CONSECUTIVE_GLOBAL_ID_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <cstddef>
#include <utility>
#include "detail/config_macros.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
struct reusable_consecutive_global_id_default_increment
{
    template<typename T>
    auto operator()(T& t)
    {
        return t.fetch_add(1, std::memory_order_relaxed);
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value = std::size_t,
    const Value InitialValue = 0,
    typename Increment = reusable_consecutive_global_id_default_increment
>
class reusable_consecutive_global_id
{
    struct reusable_id
    {
        reusable_id* m_next;
        Value m_value;
    };

    static inline std::atomic<Value>& global_value()
    {
        static std::atomic<Value> globalValue = InitialValue;
        return globalValue;
    }

    static inline std::atomic<reusable_id*>& reusable_ids()
    {
        static std::atomic<reusable_id*> reusableIds;
        return reusableIds;
    }

    inline static Increment m_increment;

    reusable_id* m_reusableId = nullptr;

public:
    reusable_consecutive_global_id() noexcept
    {
        auto reusableId = reusable_ids().load(
            std::memory_order_acquire
        );

        do
        {
            if (!reusableId)
            {
                m_reusableId = new reusable_id
                {
                    .m_next = nullptr,
                    .m_value = m_increment(global_value())
                };
                break;
            }

            if (reusable_ids().compare_exchange_weak(
                reusableId,
                reusableId->m_next,
                std::memory_order_acquire,
                std::memory_order_relaxed
            ))
            {
                m_reusableId = reusableId;
            }

        } while (!m_reusableId);
    }

    reusable_consecutive_global_id(
        const reusable_consecutive_global_id&
    ) = delete;

    reusable_consecutive_global_id(
        reusable_consecutive_global_id&& other
    ) noexcept :
        m_reusableId { other.m_reusableId }
    {
        other.m_reusableId = nullptr;
    }

    ~reusable_consecutive_global_id() noexcept
    {
        if (!m_reusableId)
        {
            return;
        }

        m_reusableId->m_next = reusable_ids().load(
            std::memory_order_relaxed
        );

        while (!reusable_ids().compare_exchange_weak(
            m_reusableId->m_next,
            m_reusableId,
            std::memory_order_release,
            std::memory_order_relaxed
        ));
    }

    void operator=(
        const reusable_consecutive_global_id&
    ) = delete;

    reusable_consecutive_global_id& operator=(
        reusable_consecutive_global_id&& other
    ) noexcept
    {
        std::swap(m_reusableId, other.m_reusableId);
        return *this;
    }

    const Value& get() const noexcept
    {
        return m_reusableId->m_value;
    }

    operator const Value&() const noexcept
    {
        return get();
    }

    const Value& operator*() const noexcept
    {
        return get();
    }

    const Value* operator->() const noexcept
    {
        return &get();
    }
};

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::reusable_consecutive_global_id;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::reusable_consecutive_global_id_default_increment;

}
#endif
