#include "async_test.h"
#include <exception>
#include <source_location>
#include <typeindex>
#include "Phantom.Coroutines/detail/config_macros.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.config_globals;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.polymorphic_promise;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.tracing;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.value_awaiter;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/config_globals.h"
#include "Phantom.Coroutines/polymorphic_promise.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/tracing.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/type_traits.h"
#include "Phantom.Coroutines/value_awaiter.h"
#include "lifetime_tracker.h"
#endif

namespace Phantom::Coroutines::tracing
{

struct tracing_tests : testing::Test
{
    struct traced_event
    {
        std::any event;

        static traced_event from_event(
            const auto& event
        )
        {
            return { &event };
        }
    };

    struct traced_events_checker
    {
        std::function<void(const std::any&)> checker;

        void operator()(const std::any& event) const
        {
            checker(event);
        }
    };

    template<
        typename Filter
    >
    struct trace_sink
    {
        const traced_events_checker& checker;
        
        template<
            typename ... Args
        >
            requires requires
        {
            get<const traced_events_checker&>(std::tie(std::declval<const Args&>()...));
        }
        trace_sink(
            const Args&... args
        ) :
            checker(get<const traced_events_checker&>(std::tie(args...)))
        { }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    struct throw_on_return
    {
        std::exception_ptr exception = std::make_exception_ptr(
            std::runtime_error{
                "Exception thrown on return"
            }
        );
    };

    struct throw_on_yield
    {
        std::exception_ptr exception = std::make_exception_ptr(
            std::runtime_error{
                "Exception thrown on yield"
            }
        );
    };

    struct throw_on_await_transform
    {
        std::exception_ptr exception = std::make_exception_ptr(
            std::runtime_error{
                "Exception thrown on await_transform"
            }
        );
    };

    struct throw_on_get_return_object
    {
        std::exception_ptr exception = std::make_exception_ptr(
            std::runtime_error{
                "Exception thrown on get_return_object"
            }
        );
    };

    struct throw_on_unhandled_exception
    {
        std::exception_ptr exception = std::make_exception_ptr(
            std::runtime_error{
                "Exception thrown on unhandled_exception"
            }
        );
    };

    struct tracing_return_value_tag {};

    template<
        typename Filter
    >
    struct trace_sink_tracing_return_value
    {
        const traced_events_checker& checker;

        template<
            typename ... Args
        >
            requires requires
        {
            get<const traced_events_checker&>(std::tie(std::declval<const Args&>()...));
        }
        trace_sink_tracing_return_value(
            const Args&... args
        ) :
            checker(get<const traced_events_checker&>(std::tie(args...)))
        { }

        template<typename Event>
        std::true_type operator()(const events::should_trace_return_value<Event>&) const
        {
            return {};
        }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    struct controllable_yield_promise_base
        :
        derived_promise<task_promise<void>>
    {
        using controllable_yield_promise_base::derived_promise::derived_promise;
        using derived_promise<task_promise<void>>::await_transform;

        std::exception_ptr exception_to_throw_on_yield;

        Coroutines::detail::suspend_never await_transform(
            this auto& self,
            throw_on_yield throwOnYield)
        {
            self.exception_to_throw_on_yield = throwOnYield.exception;
            return {};
        }

        Coroutines::detail::suspend_never yield_value(auto&&)
        {
            if (exception_to_throw_on_yield)
            {
                std::rethrow_exception(exception_to_throw_on_yield);
            }
            return {};
        }
    };

    using test_yield_underlying_promise = polymorphic_promise<
        controllable_yield_promise_base
    >;

    template<
        typename Filter
    >
    using test_traced_yield_promise = traced_promise<
        trace_sink<Filter>,
        test_yield_underlying_promise
    >;

    template<
        typename Filter
    >
    using test_traced_yield_promise_tracing_return_value = traced_promise<
        trace_sink_tracing_return_value<Filter>,
        test_yield_underlying_promise
    >;

    using test_traced_yield_task = basic_task<test_yield_underlying_promise>;

    template<
        typename Result
    >
    struct controllable_promise_base
        :
        derived_promise<task_promise<Result>>
    {
        std::exception_ptr exception_to_throw_on_return;
        std::exception_ptr exception_to_throw_on_unhandled_exception;

        using controllable_promise_base::derived_promise::derived_promise;
        using derived_promise<task_promise<Result>>::await_transform;

        Coroutines::detail::suspend_never await_transform(
            throw_on_await_transform throwOnAwaitTransform)
        {
            std::rethrow_exception(throwOnAwaitTransform.exception);
        }

        Coroutines::detail::suspend_never await_transform(
            this auto& self,
            throw_on_return throwOnReturn)
        {
            self.exception_to_throw_on_return = throwOnReturn.exception;
            return {};
        }

        Coroutines::detail::suspend_never await_transform(
            this auto& self,
            throw_on_unhandled_exception throwOnUnhandledException)
        {
            self.exception_to_throw_on_unhandled_exception = throwOnUnhandledException.exception;
            return {};
        }

        void unhandled_exception()
        {
            if (exception_to_throw_on_unhandled_exception)
            {
                std::rethrow_exception(exception_to_throw_on_unhandled_exception);
            }
            derived_promise<task_promise<Result>>::unhandled_exception();
        }
    };

    template<
        typename Result
    >
    struct controllable_promise_return_value_or_void
        :
        controllable_promise_base<Result>
    {
        using controllable_promise_base<Result>::controllable_promise_base;

        void return_value(
            auto&& value)
        {
            if (this->exception_to_throw_on_return)
            {
                std::rethrow_exception(this->exception_to_throw_on_return);
            }
            this->controllable_promise_base<Result>::return_value(
                std::forward<decltype(value)>(value));
        }
    };

    template<
    >
    struct controllable_promise_return_value_or_void<
        void
    >
        :
        controllable_promise_base<void>
    {
        using controllable_promise_base<void>::controllable_promise_base;

        void return_void()
        {
            if (this->exception_to_throw_on_return)
            {
                std::rethrow_exception(this->exception_to_throw_on_return);
            }
            else
            {
                return this->controllable_promise_base<void>::return_void();
            }
        }
    };

    template<
        typename Result
    >
    struct controllable_promise
        :
        controllable_promise_return_value_or_void<Result>
    {
        using controllable_promise_return_value_or_void<Result>::controllable_promise_return_value_or_void;
    };

    template<
        typename Result
    >
    using test_underlying_promise = polymorphic_promise<
        controllable_promise<Result>
    >;

    template<
        typename Result
    >
    struct throwing_get_return_object_promise_base
        :
        controllable_promise_base<Result>
    {
        using controllable_promise_base<Result>::controllable_promise_base;

        [[noreturn]] static void throw_get_return_object()
        {
            throw std::runtime_error("Exception thrown on get_return_object");
        }

        auto get_return_object(this auto& self)
            -> decltype(self.template controllable_promise_base<Result>::get_return_object())
        {
            throw_get_return_object();
        }
    };

    template<
        typename Result
    >
    struct throwing_get_return_object_promise
        :
        throwing_get_return_object_promise_base<Result>
    {
        using throwing_get_return_object_promise_base<Result>::throwing_get_return_object_promise_base;
    };

    template<
        typename Result = void
    >
    using test_throwing_get_return_object_underlying_promise = polymorphic_promise<
        throwing_get_return_object_promise<Result>
    >;

    template<
        typename T = void
    >
    using test_throwing_get_return_object_task = basic_task<
        test_throwing_get_return_object_underlying_promise<T>
    >;

    template<
        typename Result,
        typename Filter
    >
    using test_traced_promise = traced_promise<
        trace_sink<Filter>,
        test_underlying_promise<Result>
    >;

    template<
        typename Result,
        typename Filter
    >
    using test_traced_promise_tracing_return_value = traced_promise<
        trace_sink_tracing_return_value<Filter>,
        test_underlying_promise<Result>
    >;

    template<
        typename T = void
    >
    using test_traced_task = basic_task<test_underlying_promise<T>>;

    // --- Infrastructure for should_capture_promise_creation_arguments tests ---

    struct should_capture_args_flag { bool value; };

    struct capture_false_type_tag {};
    struct capture_true_type_tag {};
    struct capture_bool_tag {};

    template<typename Result, typename Tag>
    struct tagged_controllable_promise
        :
        controllable_promise<Result>
    {
        using controllable_promise<Result>::controllable_promise;
    };

    template<typename Result, typename Tag>
    using test_capture_underlying_promise = polymorphic_promise<
        tagged_controllable_promise<Result, Tag>
    >;

    template<typename T = void, typename Tag = void>
    using test_capture_task = basic_task<test_capture_underlying_promise<T, Tag>>;

    template<typename Filter>
    struct trace_sink_not_capturing_promise_args
    {
        const traced_events_checker& checker;

        template<typename... Args>
            requires requires
        {
            get<const traced_events_checker&>(std::tie(std::declval<const Args&>()...));
        }
        trace_sink_not_capturing_promise_args(const Args&... args)
            : checker(get<const traced_events_checker&>(std::tie(args...)))
        {}

        std::false_type operator()(const events::should_capture_promise_creation_arguments<events::create_promise>&) const
        {
            return {};
        }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    template<typename Filter>
    struct trace_sink_always_capturing_promise_args
    {
        const traced_events_checker& checker;

        template<typename... Args>
            requires requires
        {
            get<const traced_events_checker&>(std::tie(std::declval<const Args&>()...));
        }
        trace_sink_always_capturing_promise_args(const Args&... args)
            : checker(get<const traced_events_checker&>(std::tie(args...)))
        {}

        std::true_type operator()(const events::should_capture_promise_creation_arguments<events::create_promise>&) const
        {
            return {};
        }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    template<typename Filter>
    struct trace_sink_conditionally_capturing_promise_args
    {
        const traced_events_checker& checker;
        bool capture;

        template<typename... Args>
            requires requires
        {
            get<const traced_events_checker&>(std::tie(std::declval<const Args&>()...));
            get<const should_capture_args_flag&>(std::tie(std::declval<const Args&>()...));
        }
        trace_sink_conditionally_capturing_promise_args(const Args&... args)
            : checker(get<const traced_events_checker&>(std::tie(args...)))
            , capture(get<const should_capture_args_flag&>(std::tie(args...)).value)
        {}

        bool operator()(const events::should_capture_promise_creation_arguments<events::create_promise>&) const
        {
            return capture;
        }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    template<typename Result, typename Filter>
    using test_traced_promise_not_capturing_promise_args = traced_promise<
        trace_sink_not_capturing_promise_args<Filter>,
        test_capture_underlying_promise<Result, capture_false_type_tag>
    >;

    template<typename Result, typename Filter>
    using test_traced_promise_always_capturing_promise_args = traced_promise<
        trace_sink_always_capturing_promise_args<Filter>,
        test_capture_underlying_promise<Result, capture_true_type_tag>
    >;

    template<typename Result, typename Filter>
    using test_traced_promise_conditionally_capturing_promise_args = traced_promise<
        trace_sink_conditionally_capturing_promise_args<Filter>,
        test_capture_underlying_promise<Result, capture_bool_tag>
    >;

    template<
        typename EventType
    >
    const EventType& CastEventType(
        const std::any& anyEvent)
    {
        // Get human-readable string for debugging purposes.
        using expected_event_type = const EventType*;
        std::string expectedTypeName = typeid(expected_event_type).name();
        std::string actualTypeName = anyEvent.type().name();
        EXPECT_EQ(expectedTypeName, actualTypeName);

        return *std::any_cast<expected_event_type>(anyEvent);
    }

    template<
        typename ExpectedEventType
    >
    const ExpectedEventType& CastEventType(
        const std::any& anyEvent,
        [[maybe_unused]] const ExpectedEventType& expectedEvent)
    {
        return CastEventType<ExpectedEventType>(anyEvent);
    }

    struct test_awaiter_type_lambdas
    {
        static constexpr auto await_ready_false = []() { return false; };
        static constexpr auto await_ready_true = []() { return true; };
        static auto await_ready_exception(auto exception)
        {
            return [exception]() -> bool { throw exception; };
        }
        static constexpr auto await_suspend_false = [](auto) { return false; };
        static constexpr auto await_suspend_true = [](std::coroutine_handle<> handle) { handle.resume(); return true; };
        static constexpr auto await_suspend_void = [](std::coroutine_handle<> handle) { handle.resume(); };
        static auto await_suspend_exception(auto exception)
        {
            return [exception](auto) -> auto { throw exception; };
        }
        static constexpr auto await_resume_void = []() { return; };
        static auto await_resume_value(auto value)
        {
            return [value]() { return value; };
        }
        static auto await_resume_exception(auto exception)
        {
            return [exception]() -> auto { throw exception; };
        }
    };

    template<
        typename AwaitReadyLambda,
        typename AwaitSuspendLambda,
        typename AwaitResumeLambda
    >
    struct test_awaiter_type
        :
        test_awaiter_type_lambdas
    {
        AwaitReadyLambda await_ready_lambda;
        AwaitSuspendLambda await_suspend_lambda;
        AwaitResumeLambda await_resume_lambda;

        auto await_ready(
            auto&&... args)
        {
            return await_ready_lambda(std::forward<decltype(args)>(args)...);
        }

        auto await_suspend(
            auto&&... args)
        {
            return await_suspend_lambda(std::forward<decltype(args)>(args)...);
        }

        auto await_resume(
            auto&&... args)
        {
            return await_resume_lambda(std::forward<decltype(args)>(args)...);
        }

        auto with_await_ready(auto lambda)
        {
            return test_awaiter_type<
                decltype(lambda),
                AwaitSuspendLambda,
                AwaitResumeLambda
            >
            {
                .await_ready_lambda = lambda,
                .await_suspend_lambda = await_suspend_lambda,
                .await_resume_lambda = await_resume_lambda,
            };
        }

        auto with_await_ready_false()
        {
            return with_await_ready(await_ready_false);
        }

        auto with_await_ready_true()
        {
            return with_await_ready(await_ready_true);
        }

        auto with_await_ready_exception(auto exception)
        {
            return with_await_ready(await_ready_exception(exception));
        }

        auto with_await_suspend(auto lambda)
        {
            return test_awaiter_type<
                AwaitReadyLambda,
                decltype(lambda),
                AwaitResumeLambda
            >
            {
                .await_ready_lambda = await_ready_lambda,
                .await_suspend_lambda = lambda,
                .await_resume_lambda = await_resume_lambda,
            };
        }

        auto with_await_suspend_false()
        {
            return with_await_suspend(await_suspend_false);
        }

        auto with_await_suspend_true()
        {
            return with_await_suspend(await_suspend_true);
        }

        auto with_await_suspend_void()
        {
            return with_await_suspend(await_suspend_void);
        }

        template<
            typename Result
        >
        auto with_await_suspend_exception(auto exception)
        {
            return with_await_suspend(await_suspend_exception(exception));
        }

        auto with_await_resume(auto lambda)
        {
            return test_awaiter_type<
                AwaitReadyLambda,
                AwaitSuspendLambda,
                decltype(lambda)
            >
            {
                .await_ready_lambda = await_ready_lambda,
                .await_suspend_lambda = await_suspend_lambda,
                .await_resume_lambda = lambda,
            };
        }

        auto with_await_resume_void()
        {
            return with_await_resume(await_resume_void);
        }

        auto with_await_resume_value(auto value)
        {
            return with_await_resume(await_resume_value(value));
        }

        template<
            typename Result
        >
        auto with_await_resume_exception(auto exception)
        {
            return with_await_resume(await_resume_exception(exception));
        }
    };

    auto test_awaiter()
    {
        return test_awaiter_type
        {
            .await_ready_lambda = []() {},
            .await_suspend_lambda = []() {},
            .await_resume_lambda = []() {}
        }
        .with_await_ready_true()
        .with_await_suspend_void()
        .with_await_resume_void();
    }

    template<
        typename Exception
    >
    task<> expect_exception(auto task)
    {
        try
        {
            co_await std::forward<decltype(task)>(task);
            EXPECT_FALSE(true);
        }
        catch(Exception)
        { }
    }

    template<
        typename expected_event_type
    >
    bool compare_events(
        const expected_event_type& expectedEvent,
        const std::any& actualAny
    )
    {
        auto& actualEvent = CastEventType<expected_event_type>(actualAny, expectedEvent);

        if (expectedEvent.EventData.Promise != actualEvent.EventData.Promise)
        {
            return false;
        }
        if (expectedEvent.EventData.TracedPromise != actualEvent.EventData.TracedPromise)
        {
            return false;
        }
        if (expectedEvent.EventData.Awaiter != actualEvent.EventData.Awaiter)
        {
            return false;
        }
        if (expectedEvent.EventData.TracedAwaiter != actualEvent.EventData.TracedAwaiter)
        {
            return false;
        }
        if (expectedEvent.EventType != actualEvent.EventType)
        {
            return false;
        }
        
        return true;
    }

    void expect_events_equal(
        const auto& expectedEvent,
        const std::any& actualAny
    )
    {
        EXPECT_TRUE(compare_events(expectedEvent, actualAny));
    }
};
} // namespace Phantom::Coroutines::tracing

namespace std
{
template<
    typename Result,
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_traced_task<Result>,
    Args...
>
{
    static constexpr bool has_return_value_tracing =
        (std::is_same_v<Phantom::Coroutines::tracing::tracing_tests::tracing_return_value_tag, Args> || ...);

    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = std::conditional_t<
        has_return_value_tracing,
        Phantom::Coroutines::tracing::tracing_tests::test_traced_promise_tracing_return_value<Result, filter_type>,
        Phantom::Coroutines::tracing::tracing_tests::test_traced_promise<Result, filter_type>
    >;
};

template<
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_traced_yield_task,
    Args...
>
{
    static constexpr bool has_return_value_tracing =
        (std::is_same_v<Phantom::Coroutines::tracing::tracing_tests::tracing_return_value_tag, Args> || ...);

    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = std::conditional_t<
        has_return_value_tracing,
        Phantom::Coroutines::tracing::tracing_tests::test_traced_yield_promise_tracing_return_value<filter_type>,
        Phantom::Coroutines::tracing::tracing_tests::test_traced_yield_promise<filter_type>
    >;
};

template<
    typename Result,
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_throwing_get_return_object_task<Result>,
    Args...
>
{
    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = Phantom::Coroutines::tracing::traced_promise<
        Phantom::Coroutines::tracing::tracing_tests::trace_sink<filter_type>,
        Phantom::Coroutines::tracing::tracing_tests::test_throwing_get_return_object_underlying_promise<Result>
    >;
};

template<
    typename Result,
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_capture_task<Result, Phantom::Coroutines::tracing::tracing_tests::capture_false_type_tag>,
    Args...
>
{
    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = Phantom::Coroutines::tracing::tracing_tests::test_traced_promise_not_capturing_promise_args<Result, filter_type>;
};

template<
    typename Result,
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_capture_task<Result, Phantom::Coroutines::tracing::tracing_tests::capture_true_type_tag>,
    Args...
>
{
    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = Phantom::Coroutines::tracing::tracing_tests::test_traced_promise_always_capturing_promise_args<Result, filter_type>;
};

template<
    typename Result,
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::tracing::tracing_tests::test_capture_task<Result, Phantom::Coroutines::tracing::tracing_tests::capture_bool_tag>,
    Args...
>
{
    static constexpr auto get_filter(const Args& ... args)
    {
        auto tuple = std::tie(args...);
        auto filter = Phantom::Coroutines::detail::tuple_extract_convertible_elements<
            const Phantom::Coroutines::tracing::filters::filter&
        >(tuple);

        if constexpr (std::same_as<std::tuple<>, decltype(filter)>)
        {
            return Phantom::Coroutines::tracing::filters::any_event;
        }
        else
        {
            return get<0>(filter);
        }
    }

    using filter_type = decltype(get_filter(std::declval<Args>()...));
    using promise_type = Phantom::Coroutines::tracing::tracing_tests::test_traced_promise_conditionally_capturing_promise_args<Result, filter_type>;
};

}

namespace Phantom::Coroutines::tracing
{

ASYNC_TEST_F(tracing_tests, trace_return_value_moves_value)
{
    auto filter = filters::event_type<
        events::await_resume_result,
        // Verifies that we -only- get the result event.
        events::await_resume_exception
    > && filters::awaiter_type<
        events::co_await_awaiter_type
    >;

    lifetime_statistics lifetimeStatistics;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        auto filter
        ) -> test_traced_task<void>
    {
        EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
        auto tracker = co_await value_awaiter { lifetimeStatistics.tracker() };
        EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(1, lifetimeStatistics.move_construction_count);
    };

    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&] (const std::any&)
    {
    } };

    co_await taskLambda(
        tracedEventsChecker,
        filter);

    EXPECT_EQ(1, lifetimeStatistics.move_construction_count);
}

ASYNC_TEST_F(tracing_tests, trace_return_value_of_non_movable_value_copies_value)
{
    struct value_type
    {
        lifetime_tracker tracker;

        value_type(lifetime_statistics& lifetimeStatistics)
            : tracker(lifetimeStatistics)
        {
        }

        value_type(const value_type&) = default;
        value_type(value_type&&) = delete;
    };

    static_assert(!std::is_move_constructible_v<value_type>);
    static_assert(std::is_copy_constructible_v<value_type>);
    static_assert(std::is_move_constructible_v<value_type&>);
    static_assert(std::is_copy_constructible_v<value_type&>);

    auto filter = filters::event_type<
        events::await_resume_result,
        // Verifies that we -only- get the result event.
        events::await_resume_exception
    > && filters::awaiter_type<
        events::co_await_awaiter_type
    >;

    lifetime_statistics lifetimeStatistics;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        auto filter
        ) -> test_traced_task<void>
    {
        EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
        auto awaiter = value_awaiter{ value_type { lifetimeStatistics } };
        auto result = co_await awaiter;
        static_assert(std::same_as<value_type, decltype(result)>);
        EXPECT_EQ(1, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    };

    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&] (const std::any&)
    {
    } };

    co_await taskLambda(
        tracedEventsChecker,
        filter);

    EXPECT_EQ(1, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
}

ASYNC_TEST_F(tracing_tests, trace_return_value_of_non_copyable_value_does_not_trace_value)
{
    struct value_type
    {
        lifetime_tracker tracker;

        value_type(lifetime_statistics& lifetimeStatistics)
            : tracker(lifetimeStatistics)
        {
        }

        value_type(const value_type&) = delete;
    };

    static_assert(!std::is_move_constructible_v<value_type>);
    static_assert(!std::is_copy_constructible_v<value_type>);
    static_assert(std::is_move_constructible_v<value_type&>);
    static_assert(std::is_copy_constructible_v<value_type&>);

    auto filter = filters::event_type<
        events::await_resume_result,
        // Verifies that we -only- get the result event.
        events::await_resume_exception
    > && filters::awaiter_type<
        events::co_await_awaiter_type
    >;

    lifetime_statistics lifetimeStatistics;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        auto filter
        ) -> test_traced_task<void>
    {
        EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
        auto awaiter = value_awaiter{ value_type { lifetimeStatistics } };
        auto& result = co_await awaiter;
        static_assert(std::same_as<const value_type&, decltype(result)>);
        EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
        EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    };

    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&] (const std::any&)
    {
    } };

    co_await taskLambda(
        tracedEventsChecker,
        filter);

    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
}

ASYNC_TEST_F(tracing_tests, traces_create_and_destroy_promise)
{
    auto filter = filters::event_type<
        events::create_promise,
        events::destroy_promise
    >;

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        auto filter
        ) -> test_traced_task<>
        {
            co_return;
        };
    using taskLambda_type = decltype(taskLambda);

    using expected_promise_type = test_underlying_promise<void>;
    using expected_traced_promise_type = test_traced_promise<void, decltype(filter)>;

    expected_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;
        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .PromiseCreationArguments = events::make_arguments(
                    taskLambda,
                    tracedEventsChecker,
                    filter),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::create_promise{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = actualEvent.EventData.Promise;
            expectedTracedPromise = actualEvent.EventData.TracedPromise;
            expectedEvent.EventData.Promise = expectedPromise;
            expectedEvent.EventData.TracedPromise = expectedTracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::destroy_promise{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
}

ASYNC_TEST_F(tracing_tests, traces_initial_suspend)
{
    auto filter =
        filters::awaiter_type<events::initial_suspend_awaiter_type>;

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_return;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>,
        traced_events_checker&,
        decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    // The unwrapped awaiter type - what the underlying promise's initial_suspend() returns
    using unwrapped_awaiter_type = suspend_always;
    using expected_traced_awaiter_type = decltype(std::declval<expected_traced_promise_type&>().initial_suspend());

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    unwrapped_awaiter_type* expectedAwaiter = nullptr;
    expected_traced_awaiter_type* expectedTracedAwaiter = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .Awaiter = static_cast<unwrapped_awaiter_type*>(nullptr),
                .TracedAwaiter = static_cast<expected_traced_awaiter_type*>(nullptr),
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = expectedEvent.EventData.Awaiter = actualEvent.EventData.Awaiter;
            expectedTracedAwaiter = expectedEvent.EventData.TracedAwaiter = actualEvent.EventData.TracedAwaiter;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                )
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_begin{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                )
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_begin{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 6);
}

ASYNC_TEST_F(tracing_tests, traces_final_suspend)
{
    auto filter = filters::awaiter_type<events::final_suspend_awaiter_type>;

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_return;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>,
        traced_events_checker&,
        decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    // The unwrapped awaiter type - what the underlying promise's final_suspend() returns
    using expected_awaiter_type = final_suspend_transfer;
    using expected_traced_awaiter_type = decltype(std::declval<expected_traced_promise_type&>().final_suspend());

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    expected_awaiter_type* expectedAwaiter = nullptr;
    expected_traced_awaiter_type* expectedTracedAwaiter = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .Awaiter = static_cast<expected_awaiter_type*>(nullptr),
                .TracedAwaiter = static_cast<expected_traced_awaiter_type*>(nullptr),
                .AwaiterType = events::final_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = expectedEvent.EventData.Awaiter = actualEvent.EventData.Awaiter;
            expectedTracedAwaiter = expectedEvent.EventData.TracedAwaiter = actualEvent.EventData.TracedAwaiter;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                )
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_begin{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                ),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
    // Note that await_resume is not expected for final_suspend_transfer,
    // so we only expect await_ready, await_suspend events.
    EXPECT_EQ(eventIndex, 4);
}

ASYNC_TEST_F(tracing_tests, traces_await_ready_exception)
{
    auto filter = 
        filters::awaiter_type<events::co_await_awaiter_type>
        &&
        filters::event_type<
            events::await_ready_begin,
            events::await_ready_result,
            events::await_ready_exception
        >;

    auto awaiter = test_awaiter().with_await_ready_exception(
        std::runtime_error{ "await_ready exception" });

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await awaiter;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    using expected_awaiter_type = decltype(awaiter);
    using expected_traced_awaiter_type = decltype(std::declval<expected_traced_promise_type&>().await_transform(awaiter));

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    expected_awaiter_type* expectedAwaiter = nullptr;
    expected_traced_awaiter_type* expectedTracedAwaiter = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .Awaiter = static_cast<expected_awaiter_type*>(nullptr),
                .TracedAwaiter = static_cast<expected_traced_awaiter_type*>(nullptr),
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = expectedEvent.EventData.Awaiter = actualEvent.EventData.Awaiter;
            expectedTracedAwaiter = expectedEvent.EventData.TracedAwaiter = actualEvent.EventData.TracedAwaiter;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
                .MethodException = events::value{ actualException }
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;
            
            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_await_suspend_exception)
{
    auto filter = 
        filters::awaiter_type<events::co_await_awaiter_type>
        &&
        filters::event_type<
            events::await_ready_begin,
            events::await_ready_result,
            events::await_suspend_begin,
            events::await_suspend_result,
            events::await_suspend_exception
        >;

    auto awaiter = test_awaiter()
        .with_await_ready_false()
        .with_await_suspend_exception<void>(std::runtime_error{ "await_suspend exception" });

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await awaiter;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    using expected_awaiter_type = decltype(awaiter);
    using expected_traced_awaiter_type = decltype(std::declval<expected_traced_promise_type&>().await_transform(awaiter));

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    expected_awaiter_type* expectedAwaiter = nullptr;
    expected_traced_awaiter_type* expectedTracedAwaiter = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .Awaiter = static_cast<expected_awaiter_type*>(nullptr),
                .TracedAwaiter = static_cast<expected_traced_awaiter_type*>(nullptr),
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = expectedEvent.EventData.Awaiter = actualEvent.EventData.Awaiter;
            expectedTracedAwaiter = expectedEvent.EventData.TracedAwaiter = actualEvent.EventData.TracedAwaiter;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                )
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_begin{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                ),
                .MethodException = events::value{ actualException }
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;
            
            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 4);
}

ASYNC_TEST_F(tracing_tests, traces_await_resume_exception)
{
    auto filter = 
        filters::awaiter_type<events::co_await_awaiter_type>
        &&
        filters::event_type<
            events::await_ready_begin,
            events::await_ready_result,
            events::await_suspend_begin,
            events::await_suspend_result,
            events::await_resume_begin,
            events::await_resume_exception
        >;

    auto awaiter = test_awaiter()
        .with_await_ready_true()
        .with_await_resume_exception<void>(std::runtime_error{ "await_resume exception" });

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await awaiter;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    using expected_awaiter_type = decltype(awaiter);
    using expected_traced_awaiter_type = decltype(std::declval<expected_traced_promise_type&>().await_transform(awaiter));

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    expected_awaiter_type* expectedAwaiter = nullptr;
    expected_traced_awaiter_type* expectedTracedAwaiter = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .Awaiter = static_cast<expected_awaiter_type*>(nullptr),
                .TracedAwaiter = static_cast<expected_traced_awaiter_type*>(nullptr),
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = expectedEvent.EventData.Awaiter = actualEvent.EventData.Awaiter;
            expectedTracedAwaiter = expectedEvent.EventData.TracedAwaiter = actualEvent.EventData.TracedAwaiter;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_begin{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .TracedAwaiter = expectedTracedAwaiter,
                .AwaiterType = events::co_await_awaiter_type{},
                .MethodException = events::value{ actualException }
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;
            
            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 4);
}

ASYNC_TEST_F(tracing_tests, traces_return_value)
{
    auto filter = 
        filters::event_type<
            events::return_value_begin,
            events::return_value_result
        >;

    std::string expectedReturnValue = "test return value";

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<std::string>
        {
            co_return expectedReturnValue;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<std::string>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<std::string>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .MethodArguments = events::make_arguments(expectedReturnValue)
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_value_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodArguments = events::make_arguments(expectedReturnValue)
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_value_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto result = co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(result, expectedReturnValue);
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_return_value_exception)
{
    auto filter = 
        filters::event_type<
            events::return_value_begin,
            events::return_value_exception
        >;

    std::string return_value = "test return value";
    throw_on_return throw_on_return_awaiter;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<std::string>
        {
            co_await throw_on_return_awaiter;
            co_return return_value;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<std::string>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<std::string>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .MethodArguments = events::make_arguments(return_value)
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_value_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodArguments = events::make_arguments(return_value),
                .MethodException = events::value { throw_on_return_awaiter.exception },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_value_exception{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_return_void)
{
    auto filter = 
        filters::event_type<
            events::return_void_begin,
            events::return_void_result
        >;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_return;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_void_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_void_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_return_void_exception)
{
    auto filter = 
        filters::event_type<
            events::return_void_begin,
            events::return_void_exception
        >;

    throw_on_return throw_on_return_awaiter;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await throw_on_return_awaiter;
            co_return;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_void_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodException = events::value{ throw_on_return_awaiter.exception }
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::return_void_exception{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_unhandled_exception)
{
    auto filter = 
        filters::event_type<
            events::unhandled_exception_begin,
            events::unhandled_exception_result
        >;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            throw std::runtime_error("unhandled exception");
            co_return;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::unhandled_exception_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::unhandled_exception_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_yield_value)
{
    auto filter =
        filters::event_type<
            events::yield_value_begin,
            events::yield_value_result
        >;

    int yieldedValue = 42;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_yield_task
        {
            co_yield yieldedValue;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_yield_task,
        traced_events_checker&,
        decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_yield_underlying_promise;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .MethodArguments = events::make_arguments(yieldedValue),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodArguments = events::make_arguments(yieldedValue),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_yield_value_exception)
{
    auto filter =
        filters::event_type<
            events::yield_value_begin,
            events::yield_value_exception
        >;

    int yieldedValue = 42;
    throw_on_yield throw_on_yield_awaiter;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_yield_task
        {
            co_await throw_on_yield_awaiter;
            co_yield yieldedValue;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_yield_task,
        traced_events_checker&,
        decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_yield_underlying_promise;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .MethodArguments = events::make_arguments(yieldedValue),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodArguments = events::make_arguments(yieldedValue),
                .MethodException = events::value{ throw_on_yield_awaiter.exception },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_exception{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await expect_exception<std::runtime_error>(taskLambda(tracedEventsChecker, filter));
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_should_trace_return_value)
{
    auto filter =
        filters::event_type<
            events::yield_value_begin,
            events::yield_value_result
        >;

    int yieldedValue = 42;

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter),
        tracing_return_value_tag
        ) -> test_traced_yield_task
        {
            co_yield yieldedValue;
        };

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_yield_task,
        traced_events_checker&,
        decltype(filter),
        tracing_return_value_tag
    >::promise_type;

    using expected_underlying_promise_type = test_yield_underlying_promise;
    using expected_yield_awaiter_type = Coroutines::detail::suspend_never;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .MethodArguments = events::make_arguments(yieldedValue),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodArguments = events::make_arguments(yieldedValue),
                .MethodResult = events::value{ expected_yield_awaiter_type{} },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::yield_value_result{},
                expectedEventData
            );

            // Verifies MethodResult is present in the event (type-checked by CastEventType).
            CastEventType(actualEventAny, expectedEvent);

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter, tracing_return_value_tag{});
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_unhandled_exception_exception)
{
    // When unhandled_exception() itself throws, the traced promise emits
    // unhandled_exception_exception and re-throws; the exception propagates
    // to the caller of resume() just like any other exception from that method.
    auto filter = filters::event_type<
        events::unhandled_exception_begin,
        events::unhandled_exception_exception
    >;

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::unhandled_exception_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodException = events::value{ actualException },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::unhandled_exception_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await throw_on_unhandled_exception{};
            throw std::runtime_error("body exception");
        };

    try
    {
        sync_wait(taskLambda(tracedEventsChecker, filter));
        EXPECT_FALSE(true);
    }
    catch (const std::runtime_error&) { }
    EXPECT_EQ(eventIndex, 2);

    co_return;
}


ASYNC_TEST_F(tracing_tests, traces_await_transform)
{
    auto filter = filters::event_type<
        events::await_transform_begin,
        events::await_transform_result
    >;

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_transform_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_transform_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await std::suspend_never{};
        };

    co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_await_transform_exception)
{
    auto filter = filters::event_type<
        events::await_transform_begin,
        events::await_transform_exception
    >;

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_transform_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodException = events::value{ actualException },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_transform_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_await throw_on_await_transform{};
        };

    try
    {
        sync_wait(taskLambda(tracedEventsChecker, filter));
        EXPECT_FALSE(true);
    }
    catch (const std::runtime_error&) { }
    EXPECT_EQ(eventIndex, 2);

    co_return;
}


ASYNC_TEST_F(tracing_tests, traces_get_return_object)
{
    auto filter = filters::event_type<
        events::get_return_object_begin,
        events::get_return_object_result
    >;

    using expected_traced_promise_type = std::coroutine_traits<
        test_traced_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::get_return_object_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::get_return_object_result{},
                expectedEventData
            );

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_traced_task<>
        {
            co_return;
        };

    co_await taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 2);
}

ASYNC_TEST_F(tracing_tests, traces_get_return_object_exception)
{
    auto filter = filters::event_type<
        events::get_return_object_begin,
        events::get_return_object_exception
    >;

    using expected_traced_promise_type = std::coroutine_traits<
        test_throwing_get_return_object_task<>
        , traced_events_checker&
        , decltype(filter)
    >::promise_type;

    using expected_underlying_promise_type = test_throwing_get_return_object_underlying_promise<void>;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;

    auto eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny)
    {
        ++eventIndex;
        auto checkingIndex = 0;

        if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_underlying_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::get_return_object_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = expectedEvent.EventData.Promise = actualEvent.EventData.Promise;
            expectedTracedPromise = expectedEvent.EventData.TracedPromise = actualEvent.EventData.TracedPromise;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );
        }
        else if (eventIndex == ++checkingIndex)
        {
            std::exception_ptr actualException;

            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .MethodException = events::value{ actualException },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::get_return_object_exception{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            actualException = actualEvent.EventData.MethodException.Value;

            expect_events_equal(
                expectedEvent,
                actualEventAny
            );

            EXPECT_THROW(
                std::rethrow_exception(
                    actualEvent.EventData.MethodException.Value
                ),
                std::runtime_error
            );
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    auto taskLambda = [&](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter)
        ) -> test_throwing_get_return_object_task<>
        {
            co_return;
        };

    try
    {
        auto task = taskLambda(tracedEventsChecker, filter);
        EXPECT_FALSE(true);
    }
    catch (const std::runtime_error&) { }
    EXPECT_EQ(eventIndex, 2);

    co_return;
}

ASYNC_TEST_F(tracing_tests, traces_should_capture_promise_creation_arguments_false_type)
{
    auto filter = filters::event_type<events::create_promise>;

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter) filter
        ) -> test_capture_task<void, capture_false_type_tag>
        {
            co_return;
        };

    using expected_traced_promise_type = test_traced_promise_not_capturing_promise_args<
        void,
        decltype(filter)
    >;
    using expected_promise_type = test_capture_underlying_promise<void, capture_false_type_tag>;

    int eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny) mutable
    {
        if (eventIndex == 0)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .PromiseCreationArguments = events::empty_arguments,
            };
            using expected_event_type = decltype(basic_event(
                std::source_location{},
                events::create_promise{},
                expectedEventData));

            auto& actualEvent = CastEventType<expected_event_type>(actualEventAny);
            EXPECT_NE(actualEvent.EventData.Promise, nullptr);
            EXPECT_NE(actualEvent.EventData.TracedPromise, nullptr);
        }
        else
        {
            EXPECT_FALSE(true);
        }
        ++eventIndex;
    } };

    auto task = taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 1);

    co_return;
}

ASYNC_TEST_F(tracing_tests, traces_should_capture_promise_creation_arguments_true_type)
{
    auto filter = filters::event_type<events::create_promise>;

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter) filter
        ) -> test_capture_task<void, capture_true_type_tag>
        {
            co_return;
        };
    using lambda_type = decltype(taskLambda);

    using expected_traced_promise_type = test_traced_promise_always_capturing_promise_args<
        void,
        decltype(filter)
    >;
    using expected_promise_type = test_capture_underlying_promise<void, capture_true_type_tag>;

    int eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny) mutable
    {
        if (eventIndex == 0)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .PromiseCreationArguments = events::make_arguments(
                    taskLambda,
                    tracedEventsChecker,
                    filter),
            };
            using expected_event_type = decltype(basic_event(
                std::source_location{},
                events::create_promise{},
                expectedEventData));

            auto& actualEvent = CastEventType<expected_event_type>(actualEventAny);
            EXPECT_NE(actualEvent.EventData.Promise, nullptr);
            EXPECT_NE(actualEvent.EventData.TracedPromise, nullptr);
        }
        else
        {
            EXPECT_FALSE(true);
        }
        ++eventIndex;
    } };

    auto task = taskLambda(tracedEventsChecker, filter);
    EXPECT_EQ(eventIndex, 1);

    co_return;
}

ASYNC_TEST_F(tracing_tests, traces_should_capture_promise_creation_arguments_bool_true)
{
    auto filter = filters::event_type<events::create_promise>;

    should_capture_args_flag captureFlag{ true };

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter) filter,
        should_capture_args_flag flag
        ) -> test_capture_task<void, capture_bool_tag>
        {
            co_return;
        };
    using lambda_type = decltype(taskLambda);

    using expected_traced_promise_type = test_traced_promise_conditionally_capturing_promise_args<
        void,
        decltype(filter)
    >;
    using expected_promise_type = test_capture_underlying_promise<void, capture_bool_tag>;
    using expected_optional_type = std::optional<std::tuple<
        const lambda_type&,
        const traced_events_checker&,
        const decltype(filter)&,
        const should_capture_args_flag&
    >>;

    int eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny) mutable
    {
        if (eventIndex == 0)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .PromiseCreationArguments = expected_optional_type{},
            };
            using expected_event_type = decltype(basic_event(
                std::source_location{},
                events::create_promise{},
                expectedEventData));

            auto& actualEvent = CastEventType<expected_event_type>(actualEventAny);
            EXPECT_NE(actualEvent.EventData.Promise, nullptr);
            EXPECT_NE(actualEvent.EventData.TracedPromise, nullptr);
            EXPECT_TRUE(actualEvent.EventData.PromiseCreationArguments.has_value());
        }
        else
        {
            EXPECT_FALSE(true);
        }
        ++eventIndex;
    } };

    auto task = taskLambda(tracedEventsChecker, filter, captureFlag);
    EXPECT_EQ(eventIndex, 1);

    co_return;
}

ASYNC_TEST_F(tracing_tests, traces_should_capture_promise_creation_arguments_bool_false)
{
    auto filter = filters::event_type<events::create_promise>;

    should_capture_args_flag captureFlag{ false };

    auto taskLambda = [](
        this auto& self,
        traced_events_checker& eventsChecker,
        decltype(filter) filter,
        should_capture_args_flag flag
        ) -> test_capture_task<void, capture_bool_tag>
        {
            co_return;
        };
    using lambda_type = decltype(taskLambda);

    using expected_traced_promise_type = test_traced_promise_conditionally_capturing_promise_args<
        void,
        decltype(filter)
    >;
    using expected_promise_type = test_capture_underlying_promise<void, capture_bool_tag>;
    using expected_optional_type = std::optional<std::tuple<
        const lambda_type&,
        const traced_events_checker&,
        const decltype(filter)&,
        const should_capture_args_flag&
    >>;

    int eventIndex = 0;
    traced_events_checker tracedEventsChecker;
    tracedEventsChecker = { [&](const std::any& actualEventAny) mutable
    {
        if (eventIndex == 0)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = static_cast<expected_promise_type*>(nullptr),
                .TracedPromise = static_cast<expected_traced_promise_type*>(nullptr),
                .PromiseCreationArguments = expected_optional_type{},
            };
            using expected_event_type = decltype(basic_event(
                std::source_location{},
                events::create_promise{},
                expectedEventData));

            auto& actualEvent = CastEventType<expected_event_type>(actualEventAny);
            EXPECT_NE(actualEvent.EventData.Promise, nullptr);
            EXPECT_NE(actualEvent.EventData.TracedPromise, nullptr);
            EXPECT_FALSE(actualEvent.EventData.PromiseCreationArguments.has_value());
        }
        else
        {
            EXPECT_FALSE(true);
        }
        ++eventIndex;
    } };

    auto task = taskLambda(tracedEventsChecker, filter, captureFlag);
    EXPECT_EQ(eventIndex, 1);

    co_return;
}


} // namespace phantom::coroutines::test
