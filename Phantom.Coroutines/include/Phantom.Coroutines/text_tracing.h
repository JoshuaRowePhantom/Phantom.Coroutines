#ifndef PHANTOM_COROUTINES_INCLUDE_TEXT_TRACING_H
#define PHANTOM_COROUTINES_INCLUDE_TEXT_TRACING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <source_location>
#include "tracing.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace tracing
{

template<
    typename Value,
    typename Destination
>
struct formatted_text_trace_value
{
    const Value& value;
};

template<
    typename Value,
    typename Destination,
    template<typename Value> typename Formatter
>
struct formatted_text_trace_value_formatter
    :
    Formatter<Value>
{
    using formatter_type = Formatter<Value>;

    auto format(
        const formatted_text_trace_value<Value, Destination>& formattedValue,
        auto& context
    ) const
    {
        return formatter_type::format(formattedValue.value, context);
    }

    using formatter_type::format;
    using formatter_type::parse;
};

template<
    typename TextTraceSink,
    typename Destination = TextTraceSink
>
struct text_trace_sink
{
    TextTraceSink m_textTraceSink;

    template<
        typename Event
    >
    auto operator()(
        const Event& event
    )
    {
        m_textTraceSink(
            formatted_text_trace_value<Event, Destination>
            {
                .value = event
            }
        );
    }
};

// namespace [Phantom::Coroutines::]tracing
}

// namespace Phantom::Coroutines
}

#endif
