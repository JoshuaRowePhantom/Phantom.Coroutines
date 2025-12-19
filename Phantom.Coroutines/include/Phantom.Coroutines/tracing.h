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
#include "awaiter_wrapper.h"
#include "extensible_promise.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace tracing
{

template<
    typename TraceSink
> concept is_trace_sink = true;

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
    typename EventType,
    typename EventData,
    template<typename> typename ... Accessors
>
struct event : 
    Accessors<event<EventType, EventData, Accessors...>>...
{
    using event_type = event_type<EventType>;
    using event_data_type = EventData;
    
    std::source_location SourceLocation;
    event_type EventType;
    event_data_type EventData;
};

struct empty_value
{
    using value_type = void;
    static constexpr void* Value = nullptr;
    
    friend auto operator<=>(const empty_value&, const empty_value&) = default;
};

struct empty_arguments_value
{
    using value_type = std::tuple<>;
    static constexpr value_type Value = {};

    friend auto operator<=>(const empty_arguments_value&, const empty_arguments_value&) = default;
};

constexpr empty_value empty{};
constexpr empty_arguments_value empty_arguments{ };

template<
    typename T
> concept is_empty = 
std::same_as<T, nullptr_t>
||
std::same_as<T, empty_value>
||
std::same_as<T, empty_arguments_value>;

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

PHANTOM_COROUTINES_MODULE_EXPORT
struct create_promise {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct destroy_promise {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_ready_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_suspend_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_resume_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct await_transform_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct initial_suspend_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct initial_suspend_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct initial_suspend_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct final_suspend_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct final_suspend_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct final_suspend_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct unhandled_exception_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct get_return_object_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct yield_value_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_value_exception {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_begin {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_result {};
PHANTOM_COROUTINES_MODULE_EXPORT
struct return_void_exception {};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Event,
    typename EventType
> concept is_event_type = std::same_as<typename Event::event_type::label_type, EventType>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise = empty_value,
    typename TPromiseCreationArguments = empty_arguments_value,
    typename TAwaiter = empty_value,
    typename TMethodArguments = empty_arguments_value,
    typename TMethodResult = empty_value,
    typename TMethodException = empty_value,
    typename TUnhandledException = empty_value,
    typename TYieldValue = empty_value,
    typename TReturnValue = empty_value
>
struct event_data
{
    [[no_unique_address]] TPromise Promise = empty;
    [[no_unique_address]] TPromiseCreationArguments PromiseCreationArguments = empty_arguments;
    [[no_unique_address]] TAwaiter Awaiter = empty;
    [[no_unique_address]] TMethodArguments MethodArguments = empty_arguments;
    [[no_unique_address]] TMethodResult MethodResult = empty;
    [[no_unique_address]] TMethodException MethodException = empty;
    [[no_unique_address]] TUnhandledException UnhandledException = empty;
    [[no_unique_address]] TYieldValue YieldValue = empty;
    [[no_unique_address]] TReturnValue ReturnValue = empty;

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
            .PromiseCreationArguments = combine(
                this->PromiseCreationArguments, 
                other.PromiseCreationArguments),
            .Awaiter = combine(
                this->Awaiter, 
                other.Awaiter),
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

} // namespace detail

auto call_traced_method(
    const auto& traceSink,
    auto events,
    std::source_location sourceLocation,
    const auto& baseEventData,
    std::invocable<> auto call
)
{
    using result_type = std::invoke_result_t<decltype(call)>;
    try
    {
        traceSink(
            events::basic_event(
                sourceLocation,
                events.BeginEvent,
                baseEventData));
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
            decltype(auto) result = call();
            traceSink(
                events::basic_event(
                    sourceLocation,
                    events.ResultEvent,
                    baseEventData.with(
                        events::event_data
                        {
                            .MethodResult = &result
                        })));
            return result;
        }
    }
    catch (...)
    {
        auto exception = std::current_exception();
        traceSink(
            events::basic_event(
                sourceLocation,
                events.ResultEvent,
                baseEventData.with(
                    events::event_data
                    {
                        .MethodException = &exception
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
    using wrapped_awaiter_type = typename awaiter_wrapper::awaiter_type;

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
                    .Awaiter = static_cast<wrapped_awaiter_type*>(&awaiter.awaiter()),
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
        std::tuple<const Arg&> argumentsTuple{ arg };
        events::arguments arguments{ argumentsTuple };

        return self.traced_awaiter::call_awaiter(
            detail::method_events_group
            {
                events::await_suspend_begin{},
                events::await_suspend_result{},
                events::await_suspend_exception{},
            },
            self.get_event_data(
                arguments),
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
                events::await_suspend_begin{},
                events::await_suspend_result{},
                events::await_suspend_exception{},
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

protected:
    TraceSink m_traceSink;

    template<
        typename TPromise
    >
    traced_promise_trace_sink_storage(
        TPromise& self,
        const auto& ... args
    )
        requires std::constructible_from<TraceSink, decltype(args)...>
    :
    m_traceSink{ args... }
    {
        m_traceSink(
            events::basic_event(
                std::source_location::current(),
                events::create_promise{},
                events::event_data
                {
                    .Promise = &self,
                    .PromiseCreationArguments = make_arguments(args...),
                }));
    }

    template<
        typename TPromise
    >
    traced_promise_trace_sink_storage(
        TPromise& self,
        auto& ... args
    )
    requires (
        !std::constructible_from<TraceSink, decltype(args)...>
        && std::constructible_from<TraceSink>
    )
    :
    m_traceSink{}
    {
        m_traceSink(
            events::event
            {
                .SourceLocation = std::source_location::current(),
                .EventType = events::create_promise{},
                .EventData = events::event_data
                {
                    .Promise = &self,
                }
            }
        );
    }

    auto get_event_data(
        this auto& promise
    )
    {
        return events::event_data
        {
            .Promise = &promise,
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
            baseEventData,
            call);
    }
};

template<
    is_trace_sink TraceSink,
    typename BasePromise
>
class traced_promise_yield_value
    :
    public traced_promise_trace_sink_storage<TraceSink>,
    public derived_promise<BasePromise>
{
public:
    template<
        typename TPromise
    >
    traced_promise_yield_value(
        TPromise& self,
        auto&& ... args
    ) :
        traced_promise_yield_value::traced_promise_trace_sink_storage{ self, std::forward<decltype(args)>(args)... },
        traced_promise_yield_value::derived_promise{ std::forward<decltype(args)>(args)... }
    {
    }

    template<
        typename TPromise
    >
    decltype(auto) yield_value(
        this TPromise&& promise,
        auto&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
        requires has_yield_value<BasePromise>
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
                .MethodArguments = make_arguments(value),
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
    template<
        typename TPromise,
        typename Value
    >
    decltype(auto) return_value(
        this TPromise&& promise,
        Value&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return std::forward<TPromise>(promise).template call_promise_method(
            std::forward<TPromise>(promise),
            detail::method_events_group
            {
                events::return_value_begin{},
                events::return_value_result{},
                events::return_value_exception{},
            },
            sourceLocation,
            events::event_data{},
            [&]()
            {
                return std::forward<TPromise>(promise).traced_promise_return_value_or_void<TraceSink, BasePromise>::traced_promise_yield_value::return_value(
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
    using traced_promise_return_value_or_void::traced_promise_yield_value::call_promise_method;

public:
    template<
        typename TPromise
    >
    decltype(auto) return_void(
        this TPromise&& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return std::forward<TPromise>(promise).call_promise_method(
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
                return std::forward<TPromise>(promise).traced_promise_return_value_or_void<TraceSink, BasePromise>::traced_promise_yield_value::return_void();
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
    traced_promise(
        auto&& ... args
    ) :
        traced_promise_base{ *this, std::forward<decltype(args)>(args)... }
    {
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
            detail::initial_suspend_awaiter_type{},
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
            detail::final_suspend_awaiter_type{},
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
            [&]() 
            { 
                return promise.traced_promise_base::await_transform(
                    std::forward<decltype(awaiter)>(awaiter)); 
            },
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            detail::co_await_awaiter_type{}
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
};

PHANTOM_COROUTINES_MODULE_EXPORT
namespace filters
{

struct filter
{
    constexpr std::false_type operator()(const auto&) const noexcept {
        return {};
    }

    template<
        std::derived_from<filter> Left,
        std::derived_from<filter> Right
    >
    friend constexpr auto operator&&(
        Left left,
        Right right
        ) noexcept
    {
        return [=](const auto& event)
        {
            using leftType = decltype(left(event));
            using rightType = decltype(right(event));
            if constexpr (std::same_as<std::false_type, leftType>)
            {
                return leftType{};
            }
            else if constexpr (std::same_as<std::false_type, rightType>)
            {
                return rightType{};
            }
            else if constexpr (std::same_as<std::true_type, leftType> && std::same_as<std::true_type, rightType>)
            {
                return std::true_type{};
            }
            else
            {
                return left(event) && right(event);
            }
        };
    }

    template<
        std::derived_from<filter> Left,
        std::derived_from<filter> Right
    >
    friend constexpr auto operator||(
        const Left& left, 
        const Right& right
        ) noexcept
    {
        return [=](const auto& event) 
        {
            using leftType = decltype(left(event));
            using rightType = decltype(right(event));
            if constexpr (std::same_as<std::true_type, leftType>)
            {
                return leftType{};
            }
            else if constexpr (std::same_as<std::true_type, rightType>)
            {
                return rightType{};
            } 
            else if constexpr (std::same_as<std::false_type, leftType> && std::same_as<std::false_type, rightType>)
            {
                return std::false_type{};
            } 
            else
            {
                return left(event) || right(event);
            }
        };
    }

    template<
        std::derived_from<filter> Filter
    >
    friend constexpr auto operator!(
        const Filter& filter
        ) noexcept
    {
        return [=](const auto& event) 
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
    }
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
struct event_type_filter_fn : filter
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
event_type_filter_fn<EventType...> event_type_filter;

template<
    typename Event
>
struct check_constexpr_fn
{
    template<
        std::derived_from<filter> Filter
    > constexpr auto operator()(
        Filter filter
        ) const noexcept
    {
        return decltype(filter(std::declval<Event>())){};
    }
};

template<
    typename Event
> constexpr check_constexpr_fn<Event> check_constexpr{};

constexpr auto constant_filtered_trace_sink(
    auto filter,
    auto&& traceSink
)
{
    return [traceSink = std::forward<decltype(traceSink)>(traceSink), filter](const auto& event)
    {
        if constexpr (filter(event))
        {
            traceSink(event);
        }
    };
}

constexpr auto runtime_filtered_trace_sink(
    auto filter,
    auto&& traceSink
)
{
    return [traceSink = std::forward<decltype(traceSink)>(traceSink), filter](const auto& event)
    {
        if (filter(event))
        {
            traceSink(event);
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
