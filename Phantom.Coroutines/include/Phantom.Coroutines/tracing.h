#ifndef PHANTOM_COROUTINES_INCLUDE_TRACING_H
#define PHANTOM_COROUTINES_INCLUDE_TRACING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <exception>
#include <source_location>
#include <type_traits>
#include <tuple>
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

// Base for all tracing events.
PHANTOM_COROUTINES_MODULE_EXPORT
struct event
{
    std::source_location SourceLocation;

    // Two event objects compare equal even if the source
    // location is not equal, because SourceLocation
    // is neither comparable nor reliable.
    friend auto operator<=>(const event&, const event&)
    {
        return 0 <=> 0;
    }

    friend bool operator==(const event&, const event&)
    {
        return true;
    }
};

// Base for all tracing events that include arguments
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Args
> struct arguments
{
    using arguments_type = std::tuple<const Args&...>;
    arguments_type Arguments;

    friend auto operator<=>(const arguments&, const arguments&) = default;
};

// Base for all tracing events that refer to a promise.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
>
struct promise_event
    :
    event
{
    TPromise* Promise;

    friend auto operator<=>(const promise_event&, const promise_event&) = default;
};

// Trace a promise creation
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename ... Args
>
struct create_promise
    :
    promise_event<TPromise>,
    arguments<Args...>
{
    friend auto operator<=>(const create_promise&, const create_promise&) = default;
};

// Trace a promise destruction
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
>
struct destroy_promise
    :
    promise_event<TPromise>
{
    friend auto operator<=>(const destroy_promise&, const destroy_promise&) = default;
};

// Base for all tracing events that refer to a result value,
// either from an awaiter or from the promise itself.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
>
struct result_event
{
    static constexpr bool is_void_result = false;
    using result_type = TResult;
    using result_reference_type = const TResult&;

    result_reference_type Result;

    friend auto operator<=>(const result_event&, const result_event&) = default;
};

// Base for all tracing events that refer to a void result value,
// either from an awaiter or from the promise itself.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
>
struct result_event<void>
{
    static constexpr bool is_void_result = true;
    using result_type = void;

    friend auto operator<=>(const result_event&, const result_event&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> concept is_void_result_event = T::is_void_result;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename TResult
>
struct promise_result_event
    :
    promise_event<TPromise>,
    result_event<TResult>
{
    friend auto operator<=>(const promise_result_event&, const promise_result_event&) = default;
};

// Base for all tracing events that refer to an exception,
// either from an awaiter or from the promise itself.
PHANTOM_COROUTINES_MODULE_EXPORT
struct exception_event
{
    std::exception_ptr Exception;
};

// Base for all tracing events that refer to an awaiter.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter
>
struct awaiter_event
    : event
{
    static constexpr bool is_initial_suspend = is_traced_promise_initial_suspend_awaiter<TAwaiter>;
    static constexpr bool is_final_suspend = is_traced_promise_final_suspend_awaiter<TAwaiter>;
    static constexpr bool is_co_yield = is_traced_promise_co_yield_awaiter<TAwaiter>;
    static constexpr bool is_co_await = is_traced_promise_co_await_awaiter<TAwaiter>;

    TAwaiter* Awaiter;

    friend auto operator<=>(const awaiter_event&, const awaiter_event&) = default;
};

// Trace entry to an awaiter await_ready method.

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_ready_event
    :
    awaiter_event<TAwaiter>,
    arguments<Arguments...>
{
    friend auto operator<=>(const await_ready_event&, const await_ready_event&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_ready_begin
    :
    await_ready_event<TAwaiter, Arguments...>
{
    friend auto operator<=>(const await_ready_begin&, const await_ready_begin&) = default;
};

// Trace result from an awaiter await_ready method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename TResult,
    typename ... Arguments
>
struct await_ready_result
    :
    await_ready_event<TAwaiter, Arguments...>,
    result_event<TResult>
{
    friend auto operator<=>(const await_ready_result&, const await_ready_result&) = default;
};

// Trace exception from an awaiter await_ready method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_ready_exception
    :
    await_ready_event<TAwaiter, Arguments...>,
    exception_event
{
    friend auto operator<=>(const await_ready_exception&, const await_ready_exception&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter
>
struct await_ready_events
{
    await_ready_events(const TAwaiter&) {}

    template<
        typename ... Arguments
    >
    using begin_event = await_ready_begin<TAwaiter, Arguments...>;

    template<
        typename Result,
        typename ... Arguments
    > using result_event = await_ready_result<TAwaiter, Result, Arguments...>;

    template<
        typename ... Arguments
    >
    using exception_event = await_ready_exception<TAwaiter, Arguments...>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_suspend_event
    :
    awaiter_event<TAwaiter>,
    arguments<Arguments...>
{
    friend auto operator<=>(const await_suspend_event&, const await_suspend_event&) = default;
};

// Trace entry from an awaiter await_suspend method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_suspend_begin
    :
    await_suspend_event<TAwaiter, Arguments...>
{
    friend auto operator<=>(const await_suspend_begin&, const await_suspend_begin&) = default;
};

// Trace result from an await_suspend method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename TResult,
    typename ... Arguments
>
struct await_suspend_result
    :
    await_suspend_event<TAwaiter, Arguments...>,
    result_event<TResult>
{
    friend auto operator<=>(const await_suspend_result&, const await_suspend_result&) = default;
};

// Trace exception from an awaiter await_suspend method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_suspend_exception
    :
    await_suspend_event<TAwaiter, Arguments...>,
    exception_event
{
    friend auto operator<=>(const await_suspend_exception&, const await_suspend_exception&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter
>
struct await_suspend_events
{
    await_suspend_events(const TAwaiter&) {}

    template<
        typename ... Arguments
    > using begin_event = await_suspend_begin<TAwaiter, Arguments...>;

    template<
        typename Result,
        typename ... Arguments
    > using result_event = await_suspend_result<TAwaiter, Result, Arguments...>;

    template<
        typename ... Arguments
    > using exception_event = await_suspend_exception<TAwaiter, Arguments...>;
};

// Base for all tracing events that refer to an awaiter await_ready method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_resume_event
    :
    awaiter_event<TAwaiter>,
    arguments<Arguments...>
{
    friend auto operator<=>(const await_resume_event&, const await_resume_event&) = default;
};

// Trace entry to an awaiter await_resume method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_resume_begin
    :
    await_resume_event<TAwaiter, Arguments...>
{
    friend auto operator<=>(const await_resume_begin&, const await_resume_begin&) = default;
};

// Trace result from an awaiter await_resume method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename TResult,
    typename ... Arguments
>
struct await_resume_result
    :
    await_resume_event<TAwaiter, Arguments...>,
    result_event<TResult>
{
    friend auto operator<=>(const await_resume_result&, const await_resume_result&) = default;
};

// Trace exception from an awaiter await_resume method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename ... Arguments
>
struct await_resume_exception
    :
    await_resume_event<TAwaiter, Arguments...>,
    exception_event
{
    friend auto operator<=>(const await_resume_exception&, const await_resume_exception&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter
>
struct await_resume_events
{
    await_resume_events(TAwaiter&) {}

    template<
        typename ... Arguments
    > using begin_event = await_resume_begin<TAwaiter, Arguments...>;

    template<
        typename Result,
        typename ... Arguments
    > using result_event = await_resume_result<TAwaiter, Result, Arguments...>;

    template<
        typename ... Arguments
    > using exception_event = await_resume_exception<TAwaiter, Arguments...>;
};

// Base for promise events that return an exception
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
>
struct promise_exception_event
    :
    promise_event<TPromise>,
    exception_event
{
    friend auto operator<=>(const promise_exception_event&, const promise_exception_event&) = default;
};

// Trace unhandled_exception on a promise.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
> struct unhandled_exception
    :
    promise_exception_event<TPromise>
{
    friend auto operator<=>(const unhandled_exception&, const unhandled_exception&) = default;
};

// Trace entry to an return_void method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
> struct return_void_begin
    :
    promise_event<TPromise>
{
    friend auto operator<=>(const return_void_begin&, const return_void_begin&) = default;
};

// Trace result from a return_void method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename TResult
> struct return_void_result
    :
    promise_result_event<TPromise, TResult>
{
    friend auto operator<=>(const return_void_result&, const return_void_result&) = default;
};

// Trace exception from a return_void method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
> struct return_void_exception
    :
    promise_exception_event<TPromise>
{
    friend auto operator<=>(const return_void_exception&, const return_void_exception&) = default;
};

// Trace entry to a return_value method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename Argument
> struct return_value_begin
    :
    promise_result_event<TPromise, Argument>
{
    friend auto operator<=>(const return_value_begin&, const return_value_begin&) = default;
};

// Trace result from a return_value method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename TResult
> struct return_value_result
    :
    promise_result_event<TPromise, TResult>
{
    friend auto operator<=>(const return_value_result&, const return_value_result&) = default;
};

// Trace exception from a return_value method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
> struct return_value_exception
    :
    promise_exception_event<TPromise>
{
    friend auto operator<=>(const return_value_exception&, const return_value_exception&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Argument
>
struct return_value_argument_events
{
    template<
        typename TPromise
    > using return_value_begin = events::return_value_begin<TPromise, Argument>;

    template<
        typename TPromise,
        typename TResult
    > using return_value_result = events::return_value_result<TPromise, TResult>;

    template<
        typename TPromise
    > using return_value_exception = events::return_value_exception<TPromise>;
};

// Trace entry to a yield_value method.
template<
    typename TPromise,
    typename Argument
> struct yield_value_event
    :
    promise_event<TPromise>,
    arguments<Argument>
{
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename Argument
> struct yield_value_begin
    :
    yield_value_event<TPromise, Argument>
{
    friend auto operator<=>(const yield_value_begin&, const yield_value_begin&) = default;
};

// Trace result from a yield_value method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename Argument,
    typename TResult
> struct yield_value_result
    :
    yield_value_event<TPromise, Argument>,
    result_event<TResult>
{
    friend auto operator<=>(const yield_value_result&, const yield_value_result&) = default;
};

// Trace exception from a yeild_value method.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise,
    typename Argument
> struct yield_value_exception
    :
    yield_value_event<TPromise, Argument>
{
    friend auto operator<=>(const yield_value_exception&, const yield_value_exception&) = default;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise
>
struct yield_value_argument_events
{
    template<
        typename ... Arguments
    > using yield_value_begin = events::yield_value_begin<TPromise, Arguments...>;

    template<
        typename TResult,
        typename ... Arguments
    > using yield_value_result = events::yield_value_result<TPromise, TResult, Arguments...>;

    template<
        typename ... Arguments
    > using yield_value_exception = events::yield_value_exception<TPromise, Arguments...>;
};

// namespace events
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TraceSink
> concept is_trace_sink = std::invocable<
    TraceSink,
    events::event
>;

PHANTOM_COROUTINES_MODULE_EXPORT
struct initial_suspend_awaiter
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = true;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct final_suspend_awaiter
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = true;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct co_yield_awaiter
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = true;
    static constexpr bool is_traced_promise_co_await_awaiter = false;
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct co_await_awaiter
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = false;
    static constexpr bool is_traced_promise_final_suspend_awaiter = false;
    static constexpr bool is_traced_promise_co_yield_awaiter = false;
    static constexpr bool is_traced_promise_co_await_awaiter = true;
};

namespace detail
{
template<
    typename TraceSink
>
struct trace_sink_accessor
{
    TraceSink& m_traceSink;

    auto& trace_sink() const
    {
        return m_traceSink;
    }
};

} // namespace detail

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TraceSink,
    typename Awaitable,
    typename AwaiterType
>
struct traced_awaiter :
    detail::trace_sink_accessor<TraceSink>,
    awaiter_wrapper<Awaitable>,
    AwaiterType
{
    using awaiter_wrapper = traced_awaiter::awaiter_wrapper;
    using trace_sink_accessor = traced_awaiter::trace_sink_accessor;
    using traced_awaiter::trace_sink_accessor::trace_sink;

    std::source_location m_sourceLocation;

    template<
        typename Events,
        std::invocable<> Call,
        typename... Arguments
    >
    auto call_awaiter(
        [[maybe_unused]] this auto& awaiter,
        Events,
        [[maybe_unused]] Call call,
        [[maybe_unused]] std::tuple<Arguments&...> traceArguments
    ) -> std::invoke_result_t<Call>
    {
        using wrapped_awaiter_type = typename traced_awaiter::awaiter_wrapper::awaiter_type;

        using begin_event_type = typename Events::template begin_event<
            Arguments...
        >;
        using result_type = std::invoke_result_t<Call>;
        using result_event_type = typename Events::template result_event<
            result_type,
            Arguments...
        >;
        using exception_event_type = typename Events::template exception_event<
            Arguments...
        >;

        try
        {
            awaiter.traced_awaiter::trace_sink()(
                begin_event_type
                {
                    awaiter.traced_awaiter::m_sourceLocation,
                    &awaiter,
                    traceArguments
                });

            if constexpr (std::same_as<void, result_type>)
            {
                call();
                awaiter.traced_awaiter::trace_sink()(
                    result_event_type
                    {
                        awaiter.traced_awaiter::m_sourceLocation,
                        &awaiter,
                        traceArguments,
                    });
            }
            else
            {
                decltype(auto) result = call();

                awaiter.traced_awaiter::trace_sink()(
                    result_event_type
                    {
                        awaiter.traced_awaiter::m_sourceLocation,
                        &awaiter,
                        traceArguments,
                        result,
                    });

                return result;
            }
        }
        catch (...)
        {
            awaiter.traced_awaiter::trace_sink()(
                exception_event_type
                {
                    awaiter.traced_awaiter::m_sourceLocation,
                    &awaiter,
                    traceArguments,
                    std::current_exception(),
                });
            throw;
        }
    }

    decltype(auto) await_ready(
        this auto& self
        ) noexcept(noexcept(self.awaiter_wrapper::await_ready()))
    {
        return self.traced_awaiter::call_awaiter(
            events::await_ready_events{ self },
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_ready();
            },
            std::tie()
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
            events::await_suspend_events{ self },
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_suspend(
                    std::forward<Arg>(arg));
            },
            std::tie(arg)
        );
    }

    decltype(auto) await_resume(
        this auto& self
    ) noexcept(noexcept(self.awaiter_wrapper::await_resume()))
    {
        return self.traced_awaiter::call_awaiter(
            events::await_resume_events{ self },
            [&]() -> decltype(auto)
            {
                return self.awaiter_wrapper::await_resume();
            },
            std::tie()
        );
    }

    traced_awaiter(
        std::source_location sourceLocation,
        std::invocable auto awaiterFunction,
        trace_sink_accessor traceSinkAccessor,
        AwaiterType awaiterType
    )
        :
        trace_sink_accessor{ traceSinkAccessor },
        m_sourceLocation{ sourceLocation },
        awaiter_wrapper{ std::move(awaiterFunction) },
        AwaiterType{ awaiterType }
    {
    }
};

template<
    std::invocable AwaiterFunction,
    typename TraceSink,
    typename AwaiterType
>
traced_awaiter(
    std::source_location,
    AwaiterFunction,
    detail::trace_sink_accessor<TraceSink>,
    AwaiterType
) -> traced_awaiter<
    TraceSink,
    std::invoke_result_t<AwaiterFunction>,
    AwaiterType
>;


namespace detail
{

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
        auto& ... args
    )
        requires std::constructible_from<TraceSink, decltype(args)...>
    :
    m_traceSink{ args... }
    {
        m_traceSink(
            events::create_promise<
                TPromise,
                decltype(args)&...
            >
        {
            std::source_location::current(),
                & self,
                std::tie(args...)
        });
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
            events::create_promise<
                TPromise,
                decltype(args)...
            >
        {
            std::source_location::current(),
                & self,
                std::make_tuple<const decltype(args)&...>(args...)
        });
    }

    template<
        typename TPromise,
        template<typename TBeginEventPromise> typename BeginEventType,
        template<typename TResultEventPromise, typename Result> typename ResultEventType,
        template<typename TExceptionEventPromise> typename ExceptionEventType
    >
    decltype(auto) call_promise(
        this TPromise& promise,
        std::source_location sourceLocation,
        std::invocable auto call,
        auto&& ... traceArgs
    )
    {
        using promise_type = std::remove_cvref_t<TPromise>;

        try
        {
            promise.traced_promise_trace_sink_storage::m_traceSink(
                BeginEventType<promise_type>
            {
                sourceLocation,
                    & promise,
                    std::forward<decltype(traceArgs)>(traceArgs)...
            });

            using result_type = decltype(call());
            if constexpr (std::same_as<void, result_type>)
            {
                call();

                promise.traced_promise_trace_sink_storage::m_traceSink(
                    ResultEventType<promise_type, void>
                {
                    sourceLocation,
                        & promise,
                });
            }
            else
            {
                decltype(auto) result = call();

                promise.traced_promise_trace_sink_storage::m_traceSink(
                    ResultEventType<promise_type, result_type>
                {
                    sourceLocation,
                        & promise,
                        std::forward<decltype(traceArgs)>(traceArgs)...,
                        result
                });

                return std::forward<decltype(result)>(result);
            }
        }
        catch (...)
        {
            promise.traced_promise_trace_sink_storage::m_traceSink(
                ExceptionEventType<promise_type>
            {
                sourceLocation,
                    & promise,
                    std::current_exception(),
            });
            throw;
        }
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
        return std::forward<TPromise>(promise).template call_promise<
            TPromise,
            events::yield_value_argument_events<decltype(value)>::yield_value_begin,
            events::yield_value_argument_events<decltype(value)>::yield_value_result,
            events::yield_value_argument_events<decltype(value)>::yield_value_exception
        >(
            promise,
            sourceLocation,
            [&]()
            {
                return std::forward<TPromise>(promise).traced_promise_yield_value::yield_value(
                    std::forward<decltype(value)>(value));
            },
            value,
            co_yield_awaiter{}
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
        return std::forward<TPromise>(promise).template call_promise<
            TPromise,
            events::return_value_argument_events<Value>::return_value_begin,
            events::return_value_argument_events<Value>::return_value_result,
            events::return_value_argument_events<Value>::return_value_exception
        >(
            sourceLocation,
            [&]()
            {
                return std::forward<TPromise>(promise).traced_promise_return_value_or_void::traced_promise_yield_value::return_value(
                    std::forward<Value>(value));
            },
            value
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
    using traced_promise_return_value_or_void::traced_promise_yield_value::call_promise;

public:
    template<
        typename TPromise
    >
    decltype(auto) return_void(
        this TPromise&& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return std::forward<TPromise>(promise).template call_promise<
            TPromise,
            events::return_void_begin,
            events::return_void_result,
            events::return_void_exception
        >(
            sourceLocation,
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
    :
    events::event
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
    template<
        typename Declaration
    >
    struct traced_promise_trace_sink_accessor;

protected:
    using base_promise = detail::traced_promise_base<TraceSink, BasePromise>;
    using base_promise::m_traceSink;

public:
    traced_promise(
        auto&& ... args
    ) :
        base_promise{ *this, std::forward<decltype(args)>(args)... }
    {
    }

    ~traced_promise()
    {
        m_traceSink(
            events::destroy_promise<traced_promise>
        {
            std::source_location::current(),
            this
        });
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
            [&]() { return promise.base_promise::initial_suspend(); },
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            initial_suspend_awaiter{}
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
            [&]() { return promise.base_promise::final_suspend(); },
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            final_suspend_awaiter{}
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
        promise.traced_promise::m_traceSink(
            events::unhandled_exception<TPromise>
        {
            sourceLocation,
            &promise,
            std::current_exception()
        });

        promise.base_promise::unhandled_exception();
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
                return promise.base_promise::await_transform(
                    std::forward<decltype(awaiter)>(awaiter)); 
            },
            detail::trace_sink_accessor
            {
                promise.traced_promise::m_traceSink
            },
            co_await_awaiter{}
        };
    }

    template<
        typename Awaiter
    > decltype(auto) await_transform(
        this auto& promise,
        const suppress_trace<Awaiter>& noTraceAwaiter
    )
    {
        return promise.base_promise::await_transform(
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
    constexpr std::false_type operator()(const events::event&) const noexcept {
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
        return [=](const events::event& event) {
            return left(event) && right(event);
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
        return [=](const events::event& event) {
            return left(event) || right(event);
            };
    }

    template<
        std::derived_from<filter> Filter
    >
    friend constexpr auto operator!(
        const Filter& filter
        ) noexcept
    {
        return [=](const events::event& event) {
            return !filter(event);
            };
    }
};

struct any_event_fn : filter
{
    constexpr std::true_type operator()(const events::event&) const noexcept {
        return {};
    }
};
constexpr any_event_fn any_event{};

struct has_arguments_fn : filter {
    using filter::operator();
    template<typename... Arguments>
    constexpr std::true_type operator()(const events::arguments<Arguments...>&) const noexcept {
        return {};
    }
};
constexpr has_arguments_fn has_arguments{};

struct has_void_result_fn : filter {
    using filter::operator();
    constexpr std::true_type operator()(const events::result_event<void>&) const noexcept {
        return {};
    }
};
constexpr has_void_result_fn has_void_result{};

struct has_result_fn : filter {
    using filter::operator();
    template<typename Result>
    constexpr std::true_type operator()(const events::result_event<Result>&) const noexcept {
        return {};
    }
};
constexpr has_result_fn has_result{};

struct has_exception_fn : filter {
    template<
        std::derived_from<events::event> Event
    >
    constexpr auto operator()(
        const Event&
        ) const noexcept {
        return std::is_base_of<
            events::exception_event,
            Event
        >{};
    }
};
constexpr has_exception_fn has_exception{};

struct has_promise_fn : filter {
    using filter::operator();
    template<typename TPromise>
    constexpr std::true_type operator()(const events::promise_event<TPromise>&) const noexcept {
        return {};
    }
};
constexpr has_promise_fn has_promise{};

struct has_awaiter_fn : filter {
    using filter::operator();
    template<typename Awaiter>
    constexpr std::true_type operator()(const events::awaiter_event<Awaiter>&) const noexcept {
        return {};
    }
};
constexpr has_awaiter_fn has_awaiter{};

struct is_create_promise_fn : filter {
    using filter::operator();
    template<typename TPromise, typename... Arguments>
    constexpr std::true_type operator()(const events::create_promise<TPromise, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_create_promise_fn is_create_promise{};

struct is_destroy_promise_fn : filter {
    using filter::operator();
    template<typename TPromise>
    constexpr std::true_type operator()(const events::destroy_promise<TPromise>&) const noexcept {
        return {};
    }
};
constexpr is_destroy_promise_fn is_destroy_promise{};

struct is_await_ready_fn : filter {
    using filter::operator();
    template<typename Awaiter, typename... Arguments>
    constexpr std::true_type operator()(const events::await_ready_event<Awaiter, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_await_ready_fn is_await_ready{};

struct is_await_suspend_fn : filter {
    using filter::operator();
    template<typename Awaiter, typename... Arguments>
    constexpr std::true_type operator()(const events::await_suspend_event<Awaiter, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_await_suspend_fn is_await_suspend{};

struct is_await_resume_fn : filter {
    using filter::operator();
    template<typename Awaiter, typename... Arguments>
    constexpr std::true_type operator()(const events::await_resume_event<Awaiter, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_await_resume_fn is_await_resume{};

struct is_return_void_fn : filter {
    using filter::operator();
    template<typename TPromise>
    constexpr std::true_type operator()(const events::return_void_begin<TPromise>&) const noexcept {
        return {};
    }
};
constexpr is_return_void_fn is_return_void{};

struct is_return_value_fn : filter {
    using filter::operator();
    template<typename TPromise, typename... Arguments>
    constexpr std::true_type operator()(const events::return_value_begin<TPromise, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_return_value_fn is_return_value{};

struct is_yield_value_fn : filter {
    using filter::operator();
    template<typename TPromise, typename... Arguments>
    constexpr std::true_type operator()(const events::yield_value_event<TPromise, Arguments...>&) const noexcept {
        return {};
    }
};
constexpr is_yield_value_fn is_yield_value{};

struct is_unhandled_exception_fn : filter {
    using filter::operator();
    template<typename TPromise>
    constexpr std::true_type operator()(const events::unhandled_exception<TPromise>&) const noexcept {
        return {};
    }
};
constexpr is_unhandled_exception_fn is_unhandled_exception{};

struct is_initial_suspend_fn : filter {
    using filter::operator();
    template<typename Awaiter>
    constexpr auto operator()(const events::awaiter_event<Awaiter>& event) const noexcept {
        return std::bool_constant<event.is_initial_suspend>{};
    }
};
constexpr is_initial_suspend_fn is_initial_suspend{};

struct is_final_suspend_fn : filter {
    using filter::operator();
    template<typename Awaiter>
    constexpr auto operator()(const events::awaiter_event<Awaiter>& event) const noexcept {
        return std::bool_constant<event.is_final_suspend>{};
    }
};
constexpr is_final_suspend_fn is_final_suspend{};

struct is_co_yield_fn : filter {
    using filter::operator();
    template<typename Awaiter>
    constexpr auto operator()(const events::awaiter_event<Awaiter>& event) const noexcept {
        return std::bool_constant<event.is_co_yield>{};
    }
};
constexpr is_co_yield_fn is_co_yield{};

struct is_co_await_fn : filter {
    using filter::operator();
    template<typename Awaiter>
    constexpr auto operator()(const events::awaiter_event<Awaiter>& event) const noexcept {
        return std::bool_constant< event.is_co_await>{};
    }
};
constexpr is_co_await_fn is_co_await{};

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
