#ifndef PHANTOM_COROUTINES_INCLUDE_VALUE_AWAITER_H
#define PHANTOM_COROUTINES_INCLUDE_VALUE_AWAITER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <utility>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Value
>
struct value_awaiter
{
    Value m_value;

    bool await_ready() const noexcept
    {
        return true;
    }

    void await_suspend(auto&&...) const noexcept
    {
    }

    template<
        typename Self
    >
    decltype(auto) await_resume(
        this Self&& self
    )
    {
        if constexpr (std::is_rvalue_reference_v<Value>)
        {
            return std::move(self.m_value);
        }
        else if constexpr (std::is_reference_v<Value>)
        {
            return self.m_value;
        } 
        else
        {
            return std::as_const(self.m_value);
        }
    }

    // This allows value_awaiter to be used as an r-value and get r-value semantics from the co_await.
    // If we're of value_type, we remap to Value&& to move the value out.
    decltype(auto) operator co_await(
        this auto&& self)
    {
        if constexpr (
            std::is_rvalue_reference_v<decltype(self)>
            && !std::is_reference_v<Value>)
        {
            return value_awaiter<Value&&>{ std::move(self.m_value) };
        }
        else
        {
            return self;
        }
    }
};

}
#endif
