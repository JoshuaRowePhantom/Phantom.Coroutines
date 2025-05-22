#ifndef PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#define PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
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

    Value await_resume() const noexcept
    {
        return m_value;
    }
};

}
#endif
