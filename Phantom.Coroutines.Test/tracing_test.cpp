#include "async_test.h"
#include <source_location>
#include <typeindex>
#include "Phantom.Coroutines/detail/config_macros.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.config_globals;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.polymorphic_promise;
import Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.tracing;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/config_globals.h"
#include "Phantom.Coroutines/polymorphic_promise.h"
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/tracing.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/type_traits.h"
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
        
        trace_sink(
            auto&... args
        ) :
            checker(get<const traced_events_checker&>(std::tie(args...)))
        { }

        trace_sink(
            const trace_sink& other
        ) : checker{ other.checker }
        {
        }

        trace_sink(
            trace_sink& other
        ) : checker{ other.checker }
        {
        }

        void operator()(const auto& traceEvent) const
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    template<
        typename Result
    >
    using test_underlying_promise = polymorphic_promise<
        task_promise<Result>
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
        typename T = void
    >
    using test_traced_task = basic_task<polymorphic_promise<task_promise<T>>>;

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

    void ExpectIsInitialSuspend(
        const auto& event
    )
    {
        static_assert(std::same_as<
            decltype(event.EventData.AwaiterType), 
            events::initial_suspend_awaiter_type
        >);

        EXPECT_EQ(true, event.EventData.AwaiterType.is_traced_promise_initial_suspend_awaiter);
        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_co_await_awaiter);
        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_co_yield_awaiter);
        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_final_suspend_awaiter);
    }

    void ExpectIsFinalSuspend(
        const auto& event
    )
    {
        static_assert(std::same_as<
            decltype(event.EventData.AwaiterType),
            events::final_suspend_awaiter_type
        >);

        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_initial_suspend_awaiter);
        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_co_await_awaiter);
        EXPECT_EQ(false, event.EventData.AwaiterType.is_traced_promise_co_yield_awaiter);
        EXPECT_EQ(true, event.EventData.AwaiterType.is_traced_promise_final_suspend_awaiter);
    }

    void ExpectIsCoAwait(
        const auto* event
    )
    {
        EXPECT_EQ(false, event->is_initial_suspend);
        EXPECT_EQ(true, event->is_co_await);
        EXPECT_EQ(false, event->is_co_yield);
        EXPECT_EQ(false, event->is_final_suspend);
    }

    void ExpectIsCoYield(
        const auto* event
    )
    {
        EXPECT_EQ(false, event->is_initial_suspend);
        EXPECT_EQ(false, event->is_co_await);
        EXPECT_EQ(true, event->is_co_yield);
        EXPECT_EQ(false, event->is_final_suspend);
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
    using promise_type = Phantom::Coroutines::tracing::tracing_tests::test_traced_promise<Result, filter_type>;
};

}

namespace Phantom::Coroutines::tracing
{

ASYNC_TEST_F(tracing_tests, traces_create_and_destroy_promise)
{
    auto filter = filters::event_type_filter<
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
        filters::awaiter_type_filter<events::initial_suspend_awaiter_type>;

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
    using unwrapped_awaiter_type = std::suspend_always;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    unwrapped_awaiter_type* expectedAwaiter = nullptr;

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
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = actualEvent.EventData.Promise;
            expectedTracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = actualEvent.EventData.Awaiter;

            ExpectIsInitialSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
                .MethodResult = events::value { false },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsInitialSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
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

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsInitialSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
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

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsInitialSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsInitialSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::initial_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_result{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsInitialSuspend(actualEvent);
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
}

ASYNC_TEST_F(tracing_tests, traces_final_suspend)
{
    auto filter = filters::event_type_filter<
        events::await_ready_begin,
        events::await_ready_result,
        events::await_suspend_begin,
        events::await_suspend_result,
        events::await_resume_begin,
        events::await_resume_result
    >
        &&
        filters::awaiter_type_filter<events::final_suspend_awaiter_type>;

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
    using unwrapped_awaiter_type = std::suspend_always;

    expected_underlying_promise_type* expectedPromise = nullptr;
    expected_traced_promise_type* expectedTracedPromise = nullptr;
    unwrapped_awaiter_type* expectedAwaiter = nullptr;

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
                .AwaiterType = events::final_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);

            expectedPromise = actualEvent.EventData.Promise;
            expectedTracedPromise = actualEvent.EventData.TracedPromise;
            expectedAwaiter = actualEvent.EventData.Awaiter;

            ExpectIsFinalSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
                .MethodResult = events::value { false },
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_ready_result{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsFinalSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
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

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsFinalSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
                .MethodArguments = events::make_arguments(
                    std::coroutine_handle<expected_traced_promise_type>::from_promise(*expectedTracedPromise)
                )
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_suspend_result{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsFinalSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_begin{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsFinalSuspend(actualEvent);
        }
        else if (eventIndex == ++checkingIndex)
        {
            auto expectedEventData = events::event_data
            {
                .Promise = expectedPromise,
                .TracedPromise = expectedTracedPromise,
                .Awaiter = expectedAwaiter,
                .AwaiterType = events::final_suspend_awaiter_type{},
            };

            auto expectedEvent = basic_event(
                std::source_location(),
                events::await_resume_result{},
                expectedEventData
            );

            auto& actualEvent = CastEventType(actualEventAny, expectedEvent);
            ExpectIsFinalSuspend(actualEvent);
        }
        else
        {
            EXPECT_FALSE(true);
        }
    } };

    co_await taskLambda(tracedEventsChecker, filter);
}

} // namespace Phantom::Coroutines::tracing
