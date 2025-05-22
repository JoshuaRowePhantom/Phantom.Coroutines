#ifndef PHANTOM_COROUTINES_INCLUDE_STATEFUL_METAPROGRAMMING_H
#define PHANTOM_COROUTINES_INCLUDE_STATEFUL_METAPROGRAMMING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "Phantom.Coroutines/detail/config_macros.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::stateful_metaprogramming
{

namespace detail
{

template<
    typename Label
>
struct state_reader
{
    friend auto StateFunction(state_reader);
};

template<
    typename Label,
    typename Value
>
struct state_writer
{
    friend auto StateFunction(state_reader<Label>)
    {
        return Value{};
    }

    consteval operator bool() const
    {
        return true;
    }
};

}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value
>
constexpr bool write_state = detail::state_writer<Label, Value>{};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
constexpr bool has_state = 
    requires (detail::state_reader<Label> label) { StateFunction(label); };

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
using read_state = decltype(StateFunction(detail::state_reader<Label>{}));

}

#endif
