#ifndef PHANTOM_COROUTINES_INCLUDE_TRACING_H
#define PHANTOM_COROUTINES_INCLUDE_TRACING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <exception>
#include <source_location>
#include <type_traits>
#include <tuple>
#include <utility>
#include "detail/config.h"
#include "detail/coroutine.h"
#include "awaiter_wrapper.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace traced_promise_events
{
template<
    typename Awaiter
> concept is_traced_promise_initial_suspend_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_initial_suspend_awaiter;

template<
    typename Awaiter
> concept is_traced_promise_final_suspend_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_final_suspend_awaiter;

template<
    typename Awaiter
> concept is_traced_promise_co_yield_awaiter = std::remove_cvref_t<Awaiter>::is_traced_promise_co_yield_awaiter;

// Base for all tracing events.
struct event
{
    std::source_location SourceLocation;
};

// Base for all tracing events that refer to a promise.
template<
    typename Promise
>
struct promise_event
    :
    event
{
    Promise& Promise;
};

// Trace a promise creation
template<
    typename Promise,
    typename ... Args
>
struct create
    :
    public promise_event<Promise>
{
    using arguments_reference_type = std::tuple<const Args&...>;

    arguments_reference_type Arguments;
};

// Trace a promise destruction
template<
    typename Promise
>
struct destroy
    :
    public promise_event<Promise>
{
};

// Base for all tracing events that refer to an awaiter awaited in a promise.
template<
    typename Promise,
    typename Awaiter
>
struct awaiter_event :
    public promise_event<Promise>
{
    static constexpr bool is_initial_suspend = is_traced_promise_initial_suspend_awaiter<Awaiter>;
    static constexpr bool is_final_suspend = is_traced_promise_final_suspend_awaiter<Awaiter>;
    static constexpr bool is_co_yield = is_traced_promise_co_yield_awaiter<Awaiter>;
    static constexpr bool is_co_await = !is_initial_suspend && !is_final_suspend && !is_co_yield;

    Awaiter& Awaiter;
};

// Base for all tracing events that refer to a result value,
// either from an awaiter or from the promise itself.
template<
    typename Result,
    typename Tag = void
>
struct result_event
{
    static constexpr bool is_void_result = false;
    using result_type = Result;
    using result_reference_type = const Result&;

    result_reference_type Result;
};

// Base for all tracing events that refer to a void result value,
// either from an awaiter or from the promise itself.
template<
    typename Tag
>
struct result_event<void, Tag>
{
    static constexpr bool is_void_result = true;
    using result_type = void;
};

template<
    typename T
> concept is_void_result_event = T::is_void_result;

template<
    typename Promise,
    typename Result
>
struct promise_result_event
    :
    public promise_event<Promise>,
    public result_event<Result>
{
};

// Base for all tracing events that refer to an exception,
// either from an awaiter or from the promise itself.
struct exception_event
{
    std::exception_ptr Exception;
};

// Base for awaiter events that return a result.
template<
    typename Promise,
    typename Awaiter,
    typename Result
>
struct awaiter_result_event
    :
    public awaiter_event<Promise, Awaiter>,
    public result_event<Result>
{
};

// Base for awaiter events that return an exception.
template<
    typename Promise,
    typename Awaiter
> struct awaiter_exception_event
    :
    public awaiter_event<Promise, Awaiter>,
    public exception_event
{
};

// Trace entry to an awaiter await_ready method.
template<
    typename Promise,
    typename Awaiter
>
struct await_ready_begin
    :
    public awaiter_event<Promise, Awaiter>
{
};

// Trace result from an awaiter await_ready method.
template<
    typename Promise,
    typename Awaiter,
    typename Result
>
struct await_ready_result
    :
    public awaiter_result_event<Promise, Awaiter, Result>
{
};

// Trace exception from an awaiter await_ready method.
template<
    typename Promise,
    typename Awaiter
>
struct await_ready_exception
    :
    public awaiter_exception_event<Promise, Awaiter>
{
};

// Trace entry to an awaiter await_suspend method.
template<
    typename Promise,
    typename Awaiter,
    typename Argument
>
struct await_suspend_event
    :
    public awaiter_event<Promise, Awaiter>
{
    using argument_reference_type = const Argument&;
    argument_reference_type Argument;
};

// Trace result from an awaiter await_suspend method.
template<
    typename Promise,
    typename Awaiter,
    typename Argument
>
struct await_suspend_begin
    :
    public await_suspend_event<Promise, Awaiter, Argument>
{
};

// Trace exception from an awaiter await_suspend method.
template<
    typename Promise,
    typename Awaiter,
    typename Argument
>
struct await_suspend_exception
    :
    public await_suspend_event<Promise, Awaiter, Argument>,
    public exception_event
{
};

template<
    typename Argument
>
struct await_suspend_argument_events
{
    template<
        typename Promise,
        typename Awaiter
    > using await_suspend_begin = traced_promise_events::await_suspend_begin<Promise, Awaiter, Argument>;

    template<
        typename Promise,
        typename Awaiter
    > using await_suspend_exception = traced_promise_events::await_suspend_exception<Promise, Awaiter, Argument>;
};

// Trace entry to an awaiter await_resume method.
template<
    typename Promise,
    typename Awaiter
>
struct await_resume_begin
    :
    public awaiter_event<Promise, Awaiter>
{
};

// Trace result from an awaiter await_resume method.
template<
    typename Promise,
    typename Awaiter,
    typename Result
>
struct await_resume_result
    :
    public awaiter_result_event<Promise, Awaiter, Result>
{
};

// Trace exception from an awaiter await_resume method.
template<
    typename Promise,
    typename Awaiter
>
struct await_resume_exception
    :
    public awaiter_exception_event<Promise, Awaiter>
{
};

// Base for promise events that return an exception
template<
    typename Promise
>
struct promise_exception_event
    :
    public promise_event<Promise>,
    public exception_event
{
};

// Trace unhandled_exception on a promise.
template<
    typename Promise
> struct unhandled_exception
    :
    public promise_exception_event<Promise>
{
};

// Trace entry to an return_void method.
template<
    typename Promise
> struct return_void_begin
    :
    public promise_event<Promise>
{
};

// Trace result from a return_void method.
template<
    typename Promise,
    typename Result
> struct return_void_result
    :
    public promise_result_event<Promise, Result>
{
};

// Trace exception from a return_void method.
template<
    typename Promise
> struct return_void_exception
    :
    public promise_exception_event<Promise>
{
};

// Trace entry to a return_value method.
template<
    typename Promise,
    typename Argument
> struct return_value_begin
    :
    public promise_result_event<Promise, Argument>
{
};

// Trace result from a return_value method.
template<
    typename Promise,
    typename Result
> struct return_value_result
    :
    public promise_result_event<Promise, Result>
{
};

// Trace exception from a return_value method.
template<
    typename Promise
> struct return_value_exception
    :
    public promise_exception_event<Promise>
{
};

template<
    typename Argument
>
struct return_value_argument_events
{
    template<
        typename Promise
    > using return_value_begin = traced_promise_events::return_value_begin<Promise, Argument>;

    template<
        typename Promise,
        typename Result
    > using return_value_result = traced_promise_events::return_value_result<Promise, Result>;

    template<
        typename Promise
    > using return_value_exception = traced_promise_events::return_value_exception<Promise>;
};

// Trace entry to a yield_value method.
template<
    typename Promise,
    typename Argument
> struct yield_value_begin
    :
    public promise_result_event<Promise, Argument>
{
};

// Trace result from a yield_value method.
template<
    typename Promise,
    typename Result
> struct yield_value_result
    :
    public promise_result_event<Promise, Result>
{
};

// Trace exception from a yeild_value method.
template<
    typename Promise
> struct yield_value_exception
    :
    public promise_event<Promise>
{
};

template<
    typename Argument
>
struct yield_value_argument_events
{
    template<
        typename Promise
    > using yield_value_begin = traced_promise_events::yield_value_begin<Promise, Argument>;

    template<
        typename Promise,
        typename Result
    > using yield_value_result = traced_promise_events::yield_value_result<Promise, Result>;

    template<
        typename Promise
    > using yield_value_exception = traced_promise_events::yield_value_exception<Promise>;
};

};

template<
    typename TraceSink
> concept is_trace_sink = std::invocable<
    TraceSink,
    traced_promise_events::event
>;

namespace detail
{

template<
    typename Promise,
    typename Awaitable
>
struct traced_awaiter :
    awaiter_wrapper<Awaitable>
{
    using awaiter_wrapper = awaiter_wrapper<Awaitable>;

    std::source_location m_sourceLocation;
    Promise& m_promise;

    decltype(auto) trace_sink(
        this auto& awaiter)
    {
        return (
            awaiter
            .traced_awaiter::m_promise
            .Promise::m_traceSink
            );
    }

    template<
        typename Awaiter,
        template<typename Promise, typename Awaiter> typename BeginEventType,
        template<typename Promise, typename Awaiter, typename Result> typename ResultEventType,
        template<typename Promise, typename Awaiter> typename ExceptionEventType,
        std::invocable Call,
        typename... Args
    >
    decltype(auto) call_awaiter(
        this Awaiter& awaiter,
        Call call,
        Args&& ... traceArgs
    )
    {
        using wrapped_awaiter_type = typename traced_awaiter::awaiter_wrapper::awaiter_type;
        auto& wrapped_awaiter = awaiter.traced_awaiter::awaiter_wrapper::awaiter();

        try
        {
            awaiter.traced_awaiter::trace_sink()(
                BeginEventType<Promise, wrapped_awaiter_type>
            {
                awaiter.traced_awaiter::m_sourceLocation,
                    awaiter.traced_awaiter::m_promise,
                    wrapped_awaiter,
                    std::forward<Args>(traceArgs)...,
            });

            using result_type = decltype(call());

            // A successful await_suspend cannot generally speaking refer to the promise object,
            // as the coroutine may have been resumed and destroyed already.
            // Therefore is the event type is void, we don't trace.
            if constexpr (std::same_as<void, ResultEventType<Promise, wrapped_awaiter_type, result_type>>)
            {
                return call();
            }
            else if constexpr (std::same_as<void, result_type>)
            {
                call();
                awaiter.traced_awaiter::trace_sink()(
                    ResultEventType<Promise, wrapped_awaiter_type, void>
                {
                    awaiter.traced_awaiter::m_sourceLocation,
                        awaiter.traced_awaiter::m_promise,
                        wrapped_awaiter,
                        std::forward<Args>(traceArgs)...
                });
            }
            else
            {
                decltype(auto) result = call();

                awaiter.traced_awaiter::trace_sink()(
                    ResultEventType<Promise, wrapped_awaiter_type, result_type>
                {
                    awaiter.traced_awaiter::m_sourceLocation,
                        awaiter.traced_awaiter::m_promise,
                        wrapped_awaiter,
                        std::forward<Args>(traceArgs)...,
                        result
                });

                return result;
            }
        }
        catch (...)
        {
            awaiter.traced_awaiter::trace_sink()(
                ExceptionEventType<Promise, wrapped_awaiter_type>
            {
                awaiter.traced_awaiter::m_sourceLocation,
                    awaiter.traced_awaiter::m_promise,
                    wrapped_awaiter,
                    std::forward<Args>(traceArgs)...,
                    std::current_exception()
            });
            throw;
        }
    }


    decltype(auto) await_ready(
        [[maybe_unused]]
    std::source_location sourceLocation = std::source_location::current()
        ) noexcept(noexcept(this->awaiter_wrapper::await_ready()))
    {
        return this->traced_awaiter::call_awaiter<
            decltype(*this),
            traced_promise_events::await_ready_begin,
            traced_promise_events::await_ready_result,
            traced_promise_events::await_ready_exception
        >(
            [&]()
            {
                return this->awaiter_wrapper::await_ready();
            }
        );
    }

    template<
        typename Awaiter,
        typename Arg
    >
    decltype(auto) await_suspend(
        this Awaiter&& awaiter,
        Arg&& arg
    ) noexcept(noexcept(std::forward<Awaiter>(awaiter).awaiter_wrapper::await_suspend(std::forward<Arg>(arg))))
    {
        return awaiter.call_awaiter<
            Awaiter,
            traced_promise_events::await_suspend_argument_events<Arg>::await_suspend_begin,
            std::void_t,
            traced_promise_events::await_suspend_argument_events<Arg>::await_suspend_exception
        >(
            [&]()
            {
                return std::forward<Awaiter>(awaiter).awaiter_wrapper::await_suspend(
                    std::forward<Arg>(arg));
            },
            std::forward<Arg>(arg)
        );
    }

    template<
        typename Awaiter
    >
    decltype(auto) await_resume(
        this Awaiter&& awaiter
    ) noexcept(noexcept(std::forward<Awaiter>(awaiter).awaiter_wrapper::await_resume()))
    {
        return awaiter.traced_awaiter::call_awaiter<
            Awaiter,
            traced_promise_events::await_resume_begin,
            traced_promise_events::await_resume_result,
            traced_promise_events::await_resume_exception
        >(
            [&]()
            {
                return std::forward<Awaiter>(awaiter).awaiter_wrapper::await_resume();
            }
        );
    }

    traced_awaiter(
        std::source_location sourceLocation,
        Promise& promise,
        std::invocable auto awaiterFunction
    )
        :
        m_sourceLocation{ sourceLocation },
        m_promise{ promise },
        awaiter_wrapper{ std::move(awaiterFunction) }
    {
    }
};

template<
    typename Promise,
    typename Awaitable
>
struct traced_initial_suspend_awaiter : public traced_awaiter<Promise, Awaitable>
{
    static constexpr bool is_traced_promise_initial_suspend_awaiter = true;
    using traced_initial_suspend_awaiter::traced_awaiter::traced_awaiter;
};

template<
    typename Promise,
    typename Awaitable
>
struct traced_final_suspend_awaiter : public traced_awaiter<Promise, Awaitable>
{
    static constexpr bool is_traced_promise_final_suspend_awaiter = true;
    using traced_final_suspend_awaiter::traced_awaiter::traced_awaiter;
};

template<
    is_trace_sink TraceSink
>
class traced_promise_trace_sink_storage
{
    template<
        typename Promise,
        typename Awaitable
    >
    friend struct ::Phantom::Coroutines::detail::traced_awaiter;

protected:
    TraceSink m_traceSink;

    traced_promise_trace_sink_storage(
        auto&& ... args
    )
        requires std::constructible_from<TraceSink, decltype(args)...>
    :
    m_traceSink{ std::forward<decltype(args)>(args)... }
    {
        m_traceSink(
            traced_promise_events::create<
            traced_promise_trace_sink_storage,
            decltype(args)...
            >
        {
            std::source_location::current(),
                * this,
            { args ... }
        });
    }

    traced_promise_trace_sink_storage(
        auto&& ... args
    )
        requires !std::constructible_from<TraceSink, decltype(args)...>
    :
    m_traceSink{}
    {
        m_traceSink(
            traced_promise_events::create<
            traced_promise_trace_sink_storage,
            decltype(args)...
            >
        {
            std::source_location::current(),
                * this,
                std::make_tuple<const decltype(args)&...>(args...)
        });
    }

    template<
        typename Promise,
        template<typename Promise> typename BeginEventType,
        template<typename Promise, typename Result> typename ResultEventType,
        template<typename Promise> typename ExceptionEventType
    >
    decltype(auto) call_promise(
        this Promise& promise,
        std::source_location sourceLocation,
        std::invocable auto call,
        auto&& ... traceArgs
    )
    {
        try
        {
            promise.traced_promise_trace_sink_storage::m_traceSink(
                BeginEventType<Promise>
            {
                sourceLocation,
                    promise,
                    std::forward<decltype(traceArgs)>(traceArgs)...
            });

            using result_type = decltype(call());
            if constexpr (std::same_as<void, result_type>)
            {
                call();

                promise.traced_promise_trace_sink_storage::m_traceSink(
                    ResultEventType<Promise, void>
                {
                    sourceLocation,
                        promise,
                });
            }
            else
            {
                decltype(auto) result = call();

                promise.traced_promise_trace_sink_storage::m_traceSink(
                    ResultEventType<Promise, result_type>
                {
                    sourceLocation,
                        promise,
                        std::forward<decltype(traceArgs)>(traceArgs)...,
                        result
                });

                return std::forward<decltype(result)>(result);
            }
        }
        catch (...)
        {
            promise.traced_promise_trace_sink_storage::m_traceSink(
                ExceptionEventType<Promise>
            {
                sourceLocation,
                    promise,
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
    traced_promise_yield_value(
        auto&& ... args
    ) :
        traced_promise_yield_value::traced_promise_trace_sink_storage{ std::forward<decltype(args)>(args)... },
        traced_promise_yield_value::derived_promise{ std::forward<decltype(args)>(args)... }
    {
    }

    template<
        typename Promise
    >
    decltype(auto) yield_value(
        this Promise&& promise,
        auto&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
        requires has_yield_value<BasePromise>
    {
        return call_promise<
            Promise,
            traced_promise_events::yield_value_argument_events<decltype(value)>::yield_value_begin,
            traced_promise_events::yield_value_argument_events<decltype(value)>::yield_value_result,
            traced_promise_events::yield_value_argument_events<decltype(value)>::yield_value_exception
        >(
            promise,
            sourceLocation,
            [&]()
            {
                return std::forward<Promise>(promise).traced_promise_yield_value::yield_value(
                    std::forward<decltype(value)>(value));
            },
            value
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
        typename Promise,
        typename Value
    >
    decltype(auto) return_value(
        this Promise&& promise,
        Value&& value,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return std::forward<Promise>(promise).call_promise<
            Promise,
            traced_promise_events::return_value_argument_events<Value>::return_value_begin,
            traced_promise_events::return_value_argument_events<Value>::return_value_result,
            traced_promise_events::return_value_argument_events<Value>::return_value_exception
        >(
            sourceLocation,
            [&]()
            {
                return std::forward<Promise>(promise).traced_promise_return_value_or_void::traced_promise_yield_value::return_value(
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
        typename Promise
    >
    decltype(auto) return_void(
        this Promise&& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        return promise.call_promise<
            Promise,
            traced_promise_events::return_void_begin,
            traced_promise_events::return_void_result,
            traced_promise_events::return_void_exception
        >(
            sourceLocation,
            [&]()
            {
                return std::forward<Promise>(promise).traced_promise_return_value_or_void::traced_promise_yield_value::return_void();
            }
        );
    }
};

template<
    is_trace_sink TraceSink,
    typename BasePromise
>
using traced_promise_base = traced_promise_return_value_or_void<TraceSink, BasePromise>;

}

// Use suppress_trace to suppress tracing of an awaitable.
// Example:
//    co_await suppress_trace{ m_event.Wait() };
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
struct trace
    :
    traced_promise_events::event
{
};

template<
    is_trace_sink TraceSink,
    is_extensible_promise BasePromise
>
class traced_promise
    :
    public detail::traced_promise_base<TraceSink, BasePromise>
{
    template<
        typename Promise,
        typename Awaitable
    >
    friend struct ::Phantom::Coroutines::detail::traced_awaiter;

protected:
    using base_promise = detail::traced_promise_base<TraceSink, BasePromise>;
    using base_promise::m_traceSink;

public:

    traced_promise(
        auto&& ... args
    ) :
        base_promise{ std::forward<decltype(args)>(args)... }
    {
    }

    ~traced_promise()
    {
        m_traceSink(
            traced_promise_events::destroy<traced_promise>
        {
            std::source_location::current(),
            *this
        });
    }

    template<
        typename TracedAwaiter
    >
    struct initial_suspend_awaiter : public TracedAwaiter
    {
        static constexpr bool is_traced_promise_initial_suspend_awaiter = true;
        using TracedAwaiter::TracedAwaiter;
    };

    template<
        typename Promise
    >
    auto initial_suspend(
        this Promise& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        using awaiter_type = detail::traced_initial_suspend_awaiter<Promise, decltype(promise.base_promise::initial_suspend())>;

        return awaiter_type
        {
            sourceLocation,
            promise,
            [&]() { return promise.base_promise::initial_suspend(); }
        };
    }

    template<
        typename Promise
    >
    auto final_suspend(
        this Promise& promise,
        std::source_location sourceLocation = std::source_location::current()
    ) noexcept
    {
        using awaiter_type = detail::traced_final_suspend_awaiter<Promise, decltype(promise.base_promise::final_suspend())>;

        return awaiter_type
        {
            sourceLocation,
            promise,
            [&]() { return promise.base_promise::final_suspend(); }
        };
    }

    template<
        typename Promise
    >
    void unhandled_exception(
        this Promise& promise,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        promise.traced_promise::m_traceSink(
            traced_promise_events::unhandled_exception<Promise>
        {
            sourceLocation,
                promise,
                std::current_exception()
        });

        promise.base_promise::unhandled_exception();
    }

    template<
        typename Promise,
        typename Awaiter
    >
    auto await_transform(
        this Promise& promise,
        Awaiter&& awaiter,
        std::source_location sourceLocation = std::source_location::current()
    )
    {
        if constexpr (std::derived_from<Awaiter, trace>)
        {
            promise.m_traceSink(
                std::forward<Awaiter>(awaiter));
            return suspend_never{};
        }
        else
        {
            auto transformAwaiter = [&]() -> decltype(auto)
                {
                    return promise.base_promise::await_transform(
                        std::forward<decltype(awaiter)>(awaiter));
                };

            using transformed_awaiter_type = decltype(transformAwaiter());

            return detail::traced_awaiter<
                Promise,
                transformed_awaiter_type
            >
            {
                sourceLocation,
                    promise,
                    transformAwaiter
            };
        }
    }

    template<
        typename Promise,
        typename Awaiter
    > decltype(auto) await_transform(
        this Promise& promise,
        const suppress_trace<Awaiter>& noTraceAwaiter
    )
    {
        return promise.base_promise::await_transform(
            noTraceAwaiter.value
        );
    }
};

}


#endif
