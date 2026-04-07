#ifndef PHANTOM_COROUTINES_INCLUDE_TRACING_H
#define PHANTOM_COROUTINES_INCLUDE_TRACING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <exception>
#include <source_location>
#include <tuple>
#include <type_traits>
#include <typeindex>
#include <typeinfo>
#include <utility>
#include "detail/config_macros.h"
#include "detail/coroutine.h"
#include "detail/scope_guard.h"
#include "awaiter_wrapper.h"
#include "functional.h"
#include "extensible_promise.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace tracing
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TraceSink
> concept is_trace_sink = true;
//requires
//{
//    trace();
//    should_trace();
//    should_trace_return_value;
//};

namespace events
{
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
> concept is_traced_promise_initial_suspend_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_initial_suspend_awaiter;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
> concept is_traced_promise_final_suspend_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_final_suspend_awaiter;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
> concept is_traced_promise_co_yield_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_co_yield_awaiter;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
> concept is_traced_promise_co_await_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_co_await_awaiter;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TValue
>
struct value
{
    using value_type = TValue;
    const value_type& Value;

    friend auto operator<=>(const value&, const value&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Args
>
using arguments = value<std::tuple<const Args&...>>;

PHANTOM_COROUTINES_MODULE_EXPORT
constexpr auto make_arguments(
    const auto&... args
)
{
    return value{ std::tie(std::as_const(args)...) };
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label
>
struct event_type
{
    event_type() = default;
    event_type(
        Label
    )
    {
    }

    using label_type = Label;

    template<
        typename Label1,
        typename Label2
    >
    friend consteval bool operator==(
        const event_type<Label1>&,
        const event_type<Label2>&);

    template<
        typename Label1,
        typename Label2
    >
    friend consteval bool operator!=(
        const event_type<Label1>&,
        const event_type<Label2>&);
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label1,
    typename Label2
>
consteval bool operator==(
    const event_type<Label1>&,
    const event_type<Label2>&)
{
    return std::same_as<Label1, Label2>;
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label1,
    typename Label2
>
consteval bool operator!=(
    const event_type<Label1>&,
    const event_type<Label2>&)
{
    return !std::same_as<Label1, Label2>;
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TEventType,
    typename TEventData,
    template<typename> typename ... Accessors
>
struct event : 
    Accessors<event<TEventType, TEventData, Accessors...>>...
{
    using event_type = event_type<TEventType>;
    using event_data_type = TEventData;
    
    std::source_location SourceLocation;
    event_type EventType;
    event_data_type EventData;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct empty_value
{
    using value_type = void;
    static constexpr void* Value = nullptr;
    
    friend auto operator<=>(const empty_value&, const empty_value&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct empty_arguments_value
{
    using value_type = std::tuple<>;
    static constexpr value_type Value = {};

    friend auto operator<=>(const empty_arguments_value&, const empty_arguments_value&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
constexpr empty_value empty{};
PHANTOM_COROUTINES_MODULE_EXPORT
constexpr empty_arguments_value empty_arguments{ };

PHANTOM_COROUTINES_MODULE_EXPORT
struct no_awaiter_type
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct initial_suspend_awaiter_type
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = true;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct final_suspend_awaiter_type
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = true;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct co_yield_awaiter_type
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = true;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct co_await_awaiter_type
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = true;
};

template<
    typename T
> concept is_empty =
std::same_as<T, nullptr_t>
||
std::same_as<T, empty_value>
||
std::same_as<T, empty_arguments_value>
||
std::same_as<T, no_awaiter_type>;

template<
    typename T
> concept is_not_empty = !is_empty<T>;

template<
    typename Event
>
struct PromiseAccessor
{
    static constexpr bool has_promise = requires(Event self)
    {
        { self.Data.Promise } -> is_not_empty;
    };

    auto* promise(this auto& self)
    {
        if constexpr (has_promise)
        {
            return self.Data.Promise;
        }
        else
        {
            return &empty;
        }
    }
    
    static constexpr bool has_traced_promise = requires(Event self)
    {
        { self.Data.TracedPromise } -> is_not_empty;
    };

    auto* traced_promise(this auto& self)
    {
        if constexpr (has_traced_promise)
        {
            return self.Data.TracedPromise;
        }
        else
        {
            return &empty;
        }
    }

    static constexpr bool has_promise_creation_arguments = requires(Event self)
    {
        { self.Data.PromiseCreationArguments } -> is_not_empty;
    };

    auto* promise_creation_arguments(
        this auto& self
    )
    {
        if constexpr (has_promise_creation_arguments)
        {
            return self.Data.PromiseCreationArguments;
        }
        else
        {
            return &empty_arguments;
        }
    }
};

template<
    typename Event
>
struct AwaiterAccessor
{
    static constexpr bool has_awaiter = requires(Event self)
    {
        { self.Data.Awaiter } -> is_not_empty;
    };

    auto* awaiter(this auto& self)
    {
        if constexpr (has_awaiter)
        {
            return self.Data.Awaiter;
        }
        else
        {
            return &empty;
        }
    }

    static constexpr bool has_awaiter_type = requires(Event self)
    {
        { self.Data.AwaiterType } -> is_not_empty;
    };

    auto* awaiter_type(this auto& self)
    {
        if constexpr (has_awaiter_type)
        {
            return self.Data.AwaiterType;
        }
        else
        {
            return &empty;
        }
    }

    static constexpr bool has_traced_awaiter = requires(Event self)
    {
        { self.Data.TracedAwaiter } -> is_not_empty;
    };

    auto* traced_awaiter(this auto& self)
    {
        if constexpr (has_awaiter)
        {
            return self.Data.TracedAwaiter;
        }
        else
        {
            return &empty;
        }
    }

};

template<
    typename Event
>
struct MethodArgumentsAccessor
{
    static constexpr bool has_method_arguments = requires(Event self)
    {
        { self.Data.MethodArguments } -> is_not_empty;
    };

    auto* method_arguments(this auto& self)
    {
        if constexpr (has_method_arguments)
        {
            return self.Data.MethodArguments;
        }
        else
        {
            return &empty_arguments;
        }
    }
};

template<
    typename Event
>
struct MethodResultAccessor
{
    static constexpr bool has_method_result = requires(Event self)
    {
        { self.Data.MethodResult } -> is_not_empty;
    };

    auto* method_result(this auto& self)
    {
        if constexpr (has_method_result)
        {
            return self.Data.MethodResult;
        }
        else
        {
            return &empty;
        }
    }
};

template<
    typename Event
>
struct MethodExceptionAccessor
{
    static constexpr bool has_method_exception = requires(Event self)
    {
        { self.Data.MethodException } -> is_not_empty;
    };

    auto* method_exception(this auto& self)
    {
        if constexpr (has_method_exception)
        {
            return self.Data.MethodException;
        }
        else
        {
            return &empty;
        }
    }
};

template<
    typename Event
>
struct UnhandledExceptionAccessor
{
    static constexpr bool has_unhandled_exception = requires(Event self)
    {
        { self.Data.UnhandledException } -> is_not_empty;
    };

    auto* unhandled_exception(this auto& self)
    {
        if constexpr (has_unhandled_exception)
        {
            return self.Data.UnhandledException;
        }
        else
        {
            return &empty;
        }
    }
};

template<
    typename Event
>
struct YieldValueAccessor
{
    static constexpr bool has_yield_value = requires(Event self)
    {
        { self.Data.YieldValue } -> is_not_empty;
    };

    auto* yield_value(this auto& self)
    {
        if constexpr (has_yield_value)
        {
            return self.Data.YieldValue;
        }
        else
        {
            return &empty;
        }
    }
};

template<
    typename Event
>
struct ReturnValueAccessor
{
    static constexpr bool has_return_value = requires(Event self)
    {
        { self.Data.ReturnValue } -> is_not_empty;
    };

    auto* return_value(this auto& self)
    {
        if constexpr (has_return_value)
        {
            return self.Data.ReturnValue;
        }
        else
        {
            return &empty;
        }
    }
};

// The trace sink is _queried_ for should_capture_promise_creation_arguments<Event>
// to determine whether to capture the promise creation arguments. The query is
// in the form of:
// * Check to see if traceSink(const should_capture_promise_creation_arguments<PromiseCreationEvent>&) is accepted.
// * If it is not, then do not capture and trace the promise creation arguments.
// * If it is, check the return value:
// * If it is std::true_type, then capture and trace the promise creation arguments.
// * If it is std::false_type, then do not capture and trace the promise creation arguments
// * If it is bool, then check the value at runtime to determine
//  whether to capture and trace the promise creation arguments.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename PromiseCreationEvent
>
struct should_capture_promise_creation_arguments
{
    using event_type = PromiseCreationEvent;
};

// The trace sink is _queried_ for should_trace_return_value<Event>
// to determine whether to trace the return value. The query is
// in the form of:
// * Check to see if traceSink(const should_trace_return_value<Event>&) is accepted.
// * If it is not, then do not trace the return value.
// * If it is, check the return value:
// * If it is std::true_type, then trace the return value.
// * If it is std::false_type, then do not trace the return
// * If it is bool, then check the value at runtime to determine
//  whether to trace the return value.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Event
>
struct should_trace_return_value
{
    using event_type = Event;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_begin
{
    static constexpr bool is_begin = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_result
{
    static constexpr bool is_result = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_exception
{
    static constexpr bool is_exception = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_await_ready
{
    static constexpr bool is_await_ready = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_await_suspend
{
    static constexpr bool is_await_suspend = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_await_resume
{
    static constexpr bool is_await_resume = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_await_transform
{
    static constexpr bool is_await_transform = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_unhandled_exception
{
    static constexpr bool is_unhandled_exception = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_get_return_object
{
    static constexpr bool is_get_return_object = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_yield_value
{
    static constexpr bool is_yield_value = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_return_value
{
    static constexpr bool is_return_value = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct event_is_return_void
{
    static constexpr bool is_return_void = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct create_promise {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct destroy_promise {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_begin : event_is_await_ready, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_result : event_is_await_ready, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_exception : event_is_await_ready, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_begin : event_is_await_suspend, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_result : event_is_await_suspend, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_exception : event_is_await_suspend, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_begin : event_is_await_resume, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_result : event_is_await_resume, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_exception : event_is_await_resume, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_begin : event_is_await_transform, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_result : event_is_await_transform, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_exception : event_is_await_transform, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_begin : event_is_unhandled_exception, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_result : event_is_unhandled_exception, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_exception : event_is_unhandled_exception, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_begin : event_is_get_return_object, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_result : event_is_get_return_object, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_exception : event_is_get_return_object, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_begin : event_is_yield_value, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_result : event_is_yield_value, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_exception : event_is_yield_value, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_begin : event_is_return_value, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_result : event_is_return_value, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_exception : event_is_return_value, event_is_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_begin : event_is_return_void, event_is_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_result : event_is_return_void, event_is_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_exception : event_is_return_void, event_is_exception {};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Event,
    typename EventType
> concept is_event_type = std::same_as<typename Event::event_type::label_type, EventType>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise = empty_value,
    typename TTracedPromise = empty_value,
    typename TPromiseCreationArguments = empty_arguments_value,
    typename TAwaiter = empty_value,
    typename TTracedAwaiter = empty_value,
    typename TAwaiterType = no_awaiter_type,
    typename TMethodArguments = empty_arguments_value,
    typename TMethodResult = empty_value,
    typename TMethodException = empty_value,
    typename TUnhandledException = empty_value,
    typename TYieldValue = empty_value,
    typename TReturnValue = empty_value
>
struct event_data
{
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TPromise Promise = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TTracedPromise TracedPromise = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TPromiseCreationArguments PromiseCreationArguments = empty_arguments;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TAwaiter Awaiter = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TTracedAwaiter TracedAwaiter = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TAwaiterType AwaiterType = no_awaiter_type{};
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TMethodArguments MethodArguments = empty_arguments;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TMethodResult MethodResult = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TMethodException MethodException = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TUnhandledException UnhandledException = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TYieldValue YieldValue = empty;
    PHANTOM_COROUTINES_NO_UNIQUE_ADDRESS TReturnValue ReturnValue = empty;

    friend auto operator<=>(const event_data&, const event_data&) = default;

    static constexpr auto combine(
        const auto& lhs,
        const auto& rhs
    )
    {
        if constexpr (is_empty<std::remove_cvref_t<decltype(rhs)>>)
        {
            return lhs;
        }
        else
        {
            return rhs;
        }
    }

    auto with(
        const auto& other
    ) const
    {
        return events::event_data
        {
            .Promise = combine(
                this->Promise, 
                other.Promise),
            .TracedPromise = combine(
                this->TracedPromise,
                other.TracedPromise),
            .PromiseCreationArguments = combine(
                this->PromiseCreationArguments, 
                other.PromiseCreationArguments),
            .Awaiter = combine(
                this->Awaiter, 
                other.Awaiter),
            .TracedAwaiter = combine(
                this->TracedAwaiter,
                other.TracedAwaiter),
            .AwaiterType = combine(
                this->AwaiterType,
                other.AwaiterType),
            .MethodArguments = combine(
                this->MethodArguments, 
                other.MethodArguments),
            .MethodResult = combine(
                this->MethodResult, 
                other.MethodResult),
            .MethodException = combine(
                this->MethodException, 
                other.MethodException),
            .UnhandledException = combine(
                this->UnhandledException, 
                other.UnhandledException),
            .YieldValue = combine(
                this->YieldValue, 
                other.YieldValue),
            .ReturnValue = combine(
                this->ReturnValue, 
                other.ReturnValue),
        };
    }
};

template<
    typename EventType,
    typename EventData
>
using basic_event_type = event<
    EventType,
    EventData,
    PromiseAccessor,
    AwaiterAccessor,
    MethodArgumentsAccessor,
    MethodResultAccessor,
    MethodExceptionAccessor,
    UnhandledExceptionAccessor,
    YieldValueAccessor,
    ReturnValueAccessor
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename EventType,
    typename EventData
>
auto basic_event(
    const std::source_location& sourceLocation,
    const EventType& eventType,
    const EventData& eventData
)
{
    return basic_event_type<
        EventType,
        EventData
    >
    {
        .SourceLocation = sourceLocation,
        .EventType = eventType,
        .EventData = eventData,
    };
}

// namespace events
}

namespace detail
{

template<
    is_trace_sink TraceSink
>
struct trace_sink_accessor
{
    TraceSink m_traceSink;

    auto& trace_sink()
    {
        return m_traceSink;
    }
};

template<
    typename BeginEventType,
    typename ResultEventType,
    typename ExceptionEventType
>
struct method_events_group
{
    method_events_group(
        BeginEventType,
        ResultEventType,
        ExceptionEventType)
    { }

    using begin_event_type = BeginEventType;
    using result_event_type = ResultEventType;
    using exception_event_type = ExceptionEventType;

    BeginEventType BeginEvent;
    ResultEventType ResultEvent;
    ExceptionEventType ExceptionEvent;
};

template<
    typename TraceSink,
    typename EventType,
    typename BaseEventData,
    typename MethodResult
>
struct trace_sink_should_trace_return_value_result_type
{
    static constexpr bool can_trace_return_value = false;
    static constexpr bool should_query_for_trace_return_value = false;
};

template<
    typename EventType,
    typename BaseEventData,
    typename MethodResult
>
using should_trace_return_value_query_type = events::should_trace_return_value<
    decltype(
        std::declval<BaseEventData>().with(
                events::event_data
                {
                    .MethodResult = events::value{ std::declval<MethodResult>() }
            })
        ) > ;

template<
    typename TraceSink,
    typename EventType,
    typename BaseEventData,
    typename MethodResult
>
requires 
(
    (
        std::is_move_constructible_v<MethodResult>
        ||
        std::is_copy_constructible_v<MethodResult>
    )
    &&
    std::invocable<
        TraceSink,
        should_trace_return_value_query_type<
            EventType, 
            BaseEventData, 
            MethodResult
        >
    >
)
struct trace_sink_should_trace_return_value_result_type<
    TraceSink,
    EventType,
    BaseEventData,
    MethodResult
>
{
    using query_type = should_trace_return_value_query_type<
        EventType,
        BaseEventData,
        MethodResult
    >;

    using type = std::invoke_result_t<
        TraceSink,
        query_type>;

    static constexpr bool can_trace_return_value = 
        std::same_as<type, std::true_type>
        || std::same_as<type, bool>;

    static constexpr bool should_query_for_trace_return_value = std::same_as<type, bool>;
};

} // namespace detail

auto call_traced_method(
    const auto& traceSink,
    auto events,
    std::source_location sourceLocation,
    const auto& baseEventData,
    std::invocable<> auto call
) -> std::invoke_result_t<decltype(call)>
{
    using result_type = std::invoke_result_t<decltype(call)>;
    constexpr bool is_move_constructible = std::is_move_constructible_v<result_type>;
    constexpr bool is_copy_constructible = std::is_copy_constructible_v<result_type>;
    using trace_sink_should_trace_return_value_result_type = detail::trace_sink_should_trace_return_value_result_type<
        decltype(traceSink),
        decltype(events.ResultEvent),
        decltype(baseEventData),
        result_type>;

    constexpr bool can_trace_return_value = 
        trace_sink_should_trace_return_value_result_type::can_trace_return_value
        &&
        (
            is_move_constructible
            ||
            is_copy_constructible
            );

    constexpr bool should_query_for_trace_return_value = can_trace_return_value
        && trace_sink_should_trace_return_value_result_type::should_query_for_trace_return_value;

    auto invoke_without_tracing_return_value = [&]() -> result_type
    {
        if constexpr (std::same_as<void, result_type>)
        {
            call();
            traceSink(
                events::basic_event(
                    sourceLocation,
                    events.ResultEvent,
                    baseEventData));
        }
        else
        {
            auto uncaughtExceptions = std::uncaught_exceptions();

            Coroutines::detail::scope_guard guard = [&]()
            {
                if (std::uncaught_exceptions() != uncaughtExceptions)
                {
                    // If the number of uncaught exceptions has changed in between
                    // the call being performed and this guard being deactivated,
                    // it means an exception was thrown by the call,
                    // and we should not report a "result" type but an "exception" type.
                    return;
                };

                traceSink(
                    events::basic_event(
                        sourceLocation,
                        events.ResultEvent,
                        baseEventData));
            };

            return call();
        }
    };

    try
    {
        traceSink(
            events::basic_event(
                sourceLocation,
                events.BeginEvent,
                baseEventData));

        if constexpr (!can_trace_return_value)
        {
            return invoke_without_tracing_return_value();
        }
        else
        {
            auto invoke_with_tracing_return_value = [&]() -> result_type
            {
                decltype(auto) result = call();
                traceSink(
                    events::basic_event(
                        sourceLocation,
                        events.ResultEvent,
                        baseEventData.with(
                            events::event_data
                            {
                                .MethodResult = events::value{ result }
                            })));

                if constexpr (is_move_constructible)
                {
                    return auto(result);
                }
                else
                {
                    return result;
                }
            };

            if constexpr (!should_query_for_trace_return_value)
            {
                return invoke_with_tracing_return_value();
            }
            else
            {
                bool shouldTraceReturnValue = traceSink(
                    events::should_trace_return_value<
                        decltype(events::basic_event(
                            sourceLocation,
                            events.ResultEvent,
                            baseEventData.with(
                                events::event_data
                                {
                                    .MethodResult = events::value{ std::declval<result_type>() }
                                })))>{});
                if (shouldTraceReturnValue)
                {
                    return invoke_with_tracing_return_value();
                }
                else
                {
                    return invoke_without_tracing_return_value();
                }
            }
        }
    }
    catch (...)
    {
        auto exception = std::current_exception();
        traceSink(
            events::basic_event(
                sourceLocation,
                events.ExceptionEvent,
                baseEventData.with(
                    events::event_data
                    {
                        .MethodException = events::value{ exception }
                    })));
        throw;
    }
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_trace_sink TraceSink,
    typename Awaitable,
    typename AwaiterType,
    typename BaseEventData
>
struct traced_awaiter :
    detail::trace_sink_accessor<TraceSink>,
    awaiter_wrapper<Awaitable>,
    AwaiterType
{
    using awaiter_wrapper = awaiter_wrapper<Awaitable>;
    using trace_sink_accessor = traced_awaiter::trace_sink_accessor;
    using traced_awaiter::trace_sink_accessor::trace_sink;
    using wrapped_awaiter_type = std::remove_reference_t<typename awaiter_wrapper::awaiter_type>;

    std::source_location m_sourceLocation;
    BaseEventData m_baseEventData;

    auto call_awaiter(
        this auto& awaiter,
        auto events,
        const auto& baseEventData,
        std::invocable<> auto call
        
    ) -> std::invoke_result_t<decltype(call)>
    {
        return call_traced_method(
            awaiter.traced_awaiter::trace_sink(),
            events,
            awaiter.m_sourceLocation,
            baseEventData.with(
                events::event_data
                {
                    .Awaiter = static_cast<wrapped_awaiter_type*>(std::addressof(awaiter.awaiter())),
                    .TracedAwaiter = std::addressof(awaiter),
                    .AwaiterType = AwaiterType{},
                }),
            call);
    }

    decltype(auto) await_ready(
        this auto& self
        ) noexcept(noexcept(self.awaiter_wrapper::await_ready()))
    {
        return self.traced_awaiter::call_awaiter(
            detail::method_events_group
            {
                events::await_ready_begin{},
                events::await_ready_result{},
                events::await_ready_exception{},
            },
            self.get_event_data(
                events::empty_arguments),
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_ready();
            }
        );
    }

    template<
        typename Arg
    >
    decltype(auto) await_suspend(
        this auto& self,
        Arg&& arg
        ) noexcept(noexcept(self.awaiter_wrapper::await_suspend(std::forward<Arg>(arg))))
    {
        return self.traced_awaiter::call_awaiter(
            detail::method_events_group
            {
                events::await_suspend_begin{},
                events::await_suspend_result{},
                events::await_suspend_exception{},
            },
            self.get_event_data(
                make_arguments(arg)),
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_suspend(
                    std::forward<Arg>(arg));
            }
        );
    }

    decltype(auto) await_resume(
        this auto& self
    ) noexcept(noexcept(self.awaiter_wrapper::await_resume()))
    {
        return self.traced_awaiter::call_awaiter(
            detail::method_events_group
            {
                events::await_resume_begin{},
                events::await_resume_result{},
                events::await_resume_exception{},
            },
            self.get_event_data(
                events::empty_arguments),
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_resume();
            }
        );
    }

    traced_awaiter(
        std::source_location sourceLocation,
        std::invocable auto awaiterFunction,
        AwaiterType,
        trace_sink_accessor traceSinkAccessor,
        BaseEventData baseEventData
    )
        :
        trace_sink_accessor{ traceSinkAccessor },
        m_sourceLocation{ sourceLocation },
        awaiter_wrapper{ std::move(awaiterFunction) },
        m_baseEventData{ std::move(baseEventData) }
    {
    }

    template<
        typename ... Args
    >
    auto get_event_data(
        this auto& awaiter,
        const auto& methodArguments
    )
    {
        return awaiter.m_baseEventData.with(
            events::event_data
        {
            .Awaiter = &awaiter,
            .MethodArguments = methodArguments,
        });
    }
};

template<
    is_trace_sink TraceSink,
    std::invocable<> AwaiterFunction,
    typename AwaiterType,
    typename BaseEventData
>
traced_awaiter(
    std::source_location,
    AwaiterFunction,
    AwaiterType,
    detail::trace_sink_accessor<TraceSink>,
    BaseEventData
) -> traced_awaiter<
    TraceSink,
    std::invoke_result_t<AwaiterFunction>,
    AwaiterType,
    BaseEventData
>;


namespace detail
{

// This class stored the trace sink and produces non-result-specific tracing events.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_trace_sink TraceSink
>
class traced_promise_trace_sink_storage
{
    template<
        typename Declaration
    >
    struct traced_promise_trace_sink_accessor;

public:
    using trace_sink_type = TraceSink;

public:
    trace_sink_type m_traceSink;

    template<
        typename ... Args
    >
    requires
        is_constructible_from_promise_arguments<trace_sink_type, Args&&...>
    traced_promise_trace_sink_storage(
        Args&& ... args
    ) :
    m_traceSink(std::forward<Args>(args)...)
    {
    }

    // Allow default construction of the trace sink when arguments are provided.
    template<
        typename ... Args
    >
    requires 
        is_default_constructible_from_promise_arguments<trace_sink_type, Args&&...>
    traced_promise_trace_sink_storage(
        Args&& ... args
    ) :
    m_traceSink()
    {
    }

    auto get_event_data(
        this auto& promise
    )
    {
        return events::event_data
        {
            .Promise = &promise.get_underlying_promise(),
            .TracedPromise = &promise,
        };
    }

    decltype(auto) call_promise_method(
        this auto& promise,
        auto events,
        std::source_location sourceLocation,
        const auto& baseEventData,
        std::invocable auto call
    )
    {
        return call_traced_method(
            promise.traced_promise_trace_sink_storage::m_traceSink,
            events,
            sourceLocation,
            baseEventData.with(
                promise.get_event_data()),
            call);
    }
};

// This class embodies constructors for traced promises.
template<
    is_trace_sink TraceSink,
    typename BasePromise
>
class traced_promise_construction
    :
    public traced_promise_trace_sink_storage<TraceSink>,
    public derived_promise<BasePromise>
{
public:
    template<
        typename ... Args
    >
    requires 
        std::constructible_from<traced_promise_trace_sink_storage<TraceSink>, Args&&...>
        && 
        std::constructible_from<derived_promise<BasePromise>, Args&&...>
    traced_promise_construction(
        Args&& ... args
    ) 
        :
        traced_promise_construction::traced_promise_trace_sink_storage(std::forward<Args>(args)...),
        traced_promise_construction::derived_promise(std::forward<Args>(args)... )
    {
    }
};

// This class provides an implementation of yield_value for a promise
// if it has a yield_value implementation.
// The main template does not provide yield_value.
template<
    is_trace_sink TraceSink,
    typename BasePromise
>
class traced_promise_yield_value
    :
    public traced_promise_construction<TraceSink, BasePromise>
{
public:
    using traced_promise_yield_value::traced_promise_construction::traced_promise_construction;
};

// The specialization for promises that have yield_value.
template<
    is_trace_sink TraceSink,
    has_yield_value BasePromise
>
class traced_promise_yield_value<
    TraceSink,
    BasePromise
>
    :
    public traced_promise_construction<TraceSink, BasePromise>
{
public:
    using traced_promise_yield_value::traced_promise_construction::traced_promise_construction;

    // Trace an delegate the base class's yield_value implementation.
    template<
        typename TPromise
    >
    decltype(auto) yield_value(
        this TPromise&& promise,
        auto&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return promise.traced_promise_yield_value::call_promise_method(
            promise,
            detail::method_events_group
            {
                events::yield_value_begin{},
                events::yield_value_result{},
                events::yield_value_exception{},
            },
            sourceLocation,
            events::event_data
            {
                .MethodArguments = events::make_arguments(value),
            },
            [&]()
            {
                return std::forward<TPromise>(promise).traced_promise_yield_value::yield_value(
                    std::forward<decltype(value)>(value));
            }
        );
    }
};

template<
    is_trace_sink TraceSink,
    typename BasePromise
>
class traced_promise_return_value_or_void
    :
    public traced_promise_yield_value<TraceSink, BasePromise>
{
    using traced_promise_return_value_or_void::traced_promise_yield_value::traced_promise_yield_value;

public:
    using traced_promise_return_value_or_void::traced_promise_yield_value::call_promise_method;

    template<
        typename TPromise,
        typename Value
    >
    void return_value(
        this TPromise&& promise,
        Value&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        std::forward<TPromise>(promise).call_promise_method(
            detail::method_events_group
            {
                events::return_value_begin{},
                events::return_value_result{},
                events::return_value_exception{},
            },
            sourceLocation,
            events::event_data
            {
                .MethodArguments = events::make_arguments(value),
            },
            [&]()
            {
                std::forward<TPromise>(promise).traced_promise_return_value_or_void<TraceSink, BasePromise>::traced_promise_yield_value::return_value(
                    std::forward<Value>(value));
            }
        );
    }
};

template<
    is_trace_sink TraceSink,
    has_return_void BasePromise
>
class traced_promise_return_value_or_void<
    TraceSink,
    BasePromise
>
    :
    public traced_promise_yield_value<TraceSink, BasePromise>
{
    using traced_promise_return_value_or_void::traced_promise_yield_value::traced_promise_yield_value;

public:
    using traced_promise_return_value_or_void::traced_promise_yield_value::call_promise_method;

    template<
        typename TPromise
    >
    void return_void(
        this TPromise&& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        std::forward<TPromise>(promise).call_promise_method(
            detail::method_events_group
            {
                events::return_void_begin{},
                events::return_void_result{},
                events::return_void_exception{},
            },
            sourceLocation,
            events::event_data
            {
            },
            [&]()
            {
                std::forward<TPromise>(promise).traced_promise_return_value_or_void<TraceSink, BasePromise>::traced_promise_yield_value::return_void();
            }
        );
    }
};

template<
    is_trace_sink TraceSink,
    typename BasePromise
>
using traced_promise_base = traced_promise_return_value_or_void<TraceSink, BasePromise>;

} // namespace detail

// Use suppress_trace to suppress tracing of an awaitable.
// Example:
//    co_await suppress_trace{ m_event.Wait() };
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
>
struct suppress_trace
{
    Awaiter&& value;
};

// Use trace to send a value to the trace sink.
// Example:
//    co_await trace{ my_trace_event_information{} };
PHANTOM_COROUTINES_MODULE_EXPORT
struct trace
{
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_trace_sink TraceSink,
    is_extensible_promise BasePromise
>
class traced_promise
    :
    public detail::traced_promise_base<TraceSink, BasePromise>
{
public:
    using traced_promise_base = detail::traced_promise_base<TraceSink, BasePromise>;
    using traced_promise_base::call_promise_method;
    using traced_promise_base::get_event_data;
    using traced_promise_base::m_traceSink;

    template<
        typename Declaration
    >
    struct traced_promise_trace_sink_accessor;

public:
    template<
        typename ... Args
    >
    traced_promise(
        Args&& ... args
    )
        :
        traced_promise_base{ std::forward<Args>(args)... }
    {
        m_traceSink(
            events::basic_event(
                std::source_location::current(),
                events::create_promise{},
                events::event_data
                {
                    .Promise = &this->get_underlying_promise(),
                    .TracedPromise = this,
                    .PromiseCreationArguments = events::make_arguments(args...),
                }));
    }

    ~traced_promise()
    {
        m_traceSink(
            basic_event(
                std::source_location::current(),
                events::destroy_promise{},
                get_event_data()
            ));
    }

    template<
        typename TPromise
    >
    auto initial_suspend(
        this TPromise& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return traced_awaiter
        {
            sourceLocation,
            [&]() { return promise.traced_promise_base::initial_suspend(); },
            events::initial_suspend_awaiter_type{},
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            promise.get_event_data()
        };
    }

    template<
        typename TPromise
    >
    auto final_suspend(
        this TPromise& promise,
        std::source_location sourceLocation = std::source_location::current()
    ) noexcept
    {
        return traced_awaiter
        {
            sourceLocation,
            [&]() { return promise.traced_promise_base::final_suspend(); },
            events::final_suspend_awaiter_type{},
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            promise.get_event_data()
        };
    }

    template<
        typename TPromise
    >
    void unhandled_exception(
        this TPromise& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        promise.call_promise_method(
            detail::method_events_group
            {
                events::unhandled_exception_begin{},
                events::unhandled_exception_result{},
                events::unhandled_exception_exception{},
            },
            sourceLocation,
            events::event_data{},
            [&]()
            {
                return promise.traced_promise_base::unhandled_exception();
            }
        );
    }

    auto await_transform(
        this auto& promise,
        auto&& awaiter,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return traced_awaiter
        {
            sourceLocation,
            [&]() -> decltype(auto)
            { 
                return promise.traced_promise_base::await_transform(
                    std::forward<decltype(awaiter)>(awaiter)); 
            },
            events::co_await_awaiter_type{},
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            promise.get_event_data()
        };
    }

    template<
        typename Awaiter
    > decltype(auto) await_transform(
        this auto& promise,
        const suppress_trace<Awaiter>& noTraceAwaiter
    )
    {
        return promise.traced_promise_base::await_transform(
            noTraceAwaiter.value
        );
    }

    suspend_never await_transform(
        this auto& promise,
        std::derived_from<trace> auto& traceEvent
    )
    {
        promise.m_traceSink(
            traceEvent);
        return suspend_never{};
    }

    template<
        typename This
    >
    auto& get_underlying_promise(
        this This& self)
    {
        if constexpr (std::is_const_v<This>)
        {
            return static_cast<const BasePromise&>(self);
        }
        else
        {
            return static_cast<BasePromise&>(self);
        }
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
namespace filters
{

struct filter;

template<
    typename T
>
concept is_filter = std::derived_from<T, filter>;

template<
    is_filter Left,
    is_filter Right
>
struct and_filter;

template<
    is_filter Left,
    is_filter Right
>
struct or_filter;

template<
    is_filter Filter
>
struct not_filter;

struct filter
{
    constexpr std::false_type operator()(const auto&) const noexcept {
        return {};
    }

    template<
        is_filter Left,
        is_filter Right
    >
    friend constexpr auto operator&&(
        Left left,
        Right right
        ) noexcept
    {
        return and_filter<Left, Right>{ left, right };
    }

    template<
        is_filter Left,
        is_filter Right
    >
    friend constexpr auto operator||(
        Left left, 
        Right right
        ) noexcept
    {
        return or_filter<Left, Right>{ left, right };
    }

    template<
        is_filter Filter
    >
    friend constexpr auto operator!(
        Filter filter
        ) noexcept
    {
        return not_filter<Filter>{ filter };
    }
};

template<
    is_filter Left,
    is_filter Right
>
struct and_filter : filter
{
    Left left;
    Right right;

    constexpr bool operator()(
        const auto& event
        ) const noexcept
    {
        using leftType = decltype(left(event));
        using rightType = decltype(right(event));

        if constexpr (
            std::same_as<std::false_type, leftType>
            ||
            std::same_as<std::false_type, rightType>)
        {
            return std::false_type{};
        }
        else if constexpr (
            std::same_as<std::true_type, leftType> &&
            std::same_as<std::true_type, rightType>)
        {
            return std::true_type{};
        }
        else
        {
            return left(event) && right(event);
        }
    }
};

template<
    is_filter Left,
    is_filter Right
>
struct or_filter : filter
{
    Left left;
    Right right;

    constexpr bool operator()(
        const auto& event
        ) const noexcept
    {
        using leftType = decltype(left(event));
        using rightType = decltype(right(event));

        if constexpr (
            std::same_as<std::true_type, leftType>
            ||
            std::same_as<std::true_type, rightType>)
        {
            return std::true_type{};
        }
        else if constexpr (
            std::same_as<std::false_type, leftType> &&
            std::same_as<std::false_type, rightType>)
        {
            return std::false_type{};
        }
        else
        {
            return left(event) && right(event);
        }
    }
};

template<
    is_filter Filter
>
struct not_filter : filter
{
    Filter filter;

    constexpr auto operator()(
        const auto& event)
    {
        using type = decltype(filter(event));
        if constexpr (std::same_as<std::true_type, type>)
        {
            return std::false_type{};
        }
        else if constexpr (std::same_as<std::false_type, type>)
        {
            return std::true_type{};
        }
        else
        {
            return !filter(event);
        }
    };
};

struct any_event_fn : filter
{
    constexpr std::true_type operator()(const auto&) const noexcept {
        return {};
    }
};
constexpr any_event_fn any_event{};

template<
    typename ... EventType
>
struct event_type_fn : filter
{
    using filter::operator();
    constexpr std::true_type operator()(
        const auto& event
        ) const noexcept
        requires (
            events::is_event_type<std::remove_cvref_t<decltype(event)>, EventType> || ...
        )
    {
        return {};
    }
};

template<
    typename ... EventType
>
event_type_fn<EventType...> event_type;

template<
    typename AwaiterType
>
struct awaiter_type_fn : filter
{
    using filter::operator();
    constexpr std::true_type operator()(
        const auto& event
        ) const noexcept
        requires std::same_as<
            const decltype(event.EventData.AwaiterType)&,
            const AwaiterType&
        >
    {
        return {};
    }
};

template<
    typename AwaiterType
>
constexpr awaiter_type_fn<AwaiterType> awaiter_type;

template<
    typename Event
>
struct check_constexpr_fn
{
    template<
        is_filter Filter
    > constexpr auto operator()(
        Filter filter
        ) const noexcept
    {
        return decltype(filter(std::declval<Event>())){};
    }
};

// Return a trace sink that traces return values for events that are selected.
template<
    typename TraceSink
>
constexpr auto trace_return_value(
    TraceSink traceSink
)
{
    return composed_function
    {
        traceSink,
        []<typename Event>(const events::should_trace_return_value<Event>&)
        {
            return std::true_type{};
        }
    };
}

template<
    typename Event
> constexpr check_constexpr_fn<Event> check_constexpr{};

constexpr auto constant_filtered_trace_sink(
    auto filter,
    auto&& traceSink
)
{
    return Phantom::Coroutines::composed_function
    {
        // Queries bypass the filter and propagate to the inner sink.
        [traceSink]<typename Event>(const events::should_trace_return_value<Event>& query) -> decltype(auto)
        {
            return traceSink(query);
        },
        [traceSink]<typename Event>(const events::should_capture_promise_creation_arguments<Event>& query) -> decltype(auto)
        {
            return traceSink(query);
        },
        [traceSink, filter](const auto& event)
        {
            if constexpr (filter(event))
            {
                traceSink(event);
            }
        }
    };
}

constexpr auto runtime_filtered_trace_sink(
    auto filter,
    auto&& traceSink
)
{
    return Phantom::Coroutines::composed_function
    {
        // Queries bypass the filter and propagate to the inner sink.
        [traceSink]<typename Event>(const events::should_trace_return_value<Event>& query) -> decltype(auto)
        {
            return traceSink(query);
        },
        [traceSink]<typename Event>(const events::should_capture_promise_creation_arguments<Event>& query) -> decltype(auto)
        {
            return traceSink(query);
        },
        [traceSink, filter](const auto& event)
        {
            if (filter(event))
            {
                traceSink(event);
            }
        }
    };
}

// namespace filters
}

// namespace tracing
}


// namespace Phantom::Coroutines
}

#endif
