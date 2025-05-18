#include "async_test.h"
#include <typeindex>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.config_globals;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.tracing;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/config_globals.h"
#include "Phantom.Coroutines/tracing.h"
#include "Phantom.Coroutines/task.h"
#endif

namespace Phantom::Coroutines
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

    struct trace_sink
    {
        traced_events_checker& checker;

        trace_sink(
            auto&... args
        ) :
            checker(get<traced_events_checker&>(std::tie(args...)))
        { }

        void operator()(const auto& traceEvent)
        {
            checker(&traceEvent);
        }
    };

    template<
        typename T
    >
    using test_traced_promise = tracing::traced_promise<
        trace_sink,
        task_promise<T>
    >;

    template<
        typename T = void
    >
    using test_traced_task = basic_task<test_traced_promise<T>>;
};

template<
    typename EventType
>
auto CastEventType(
    const std::any& anyEvent)
{
    // Get human-readable string for debugging purposes.
    std::string expectedTypeName = typeid(const EventType*).name();
    std::string actualTypeName = anyEvent.type().name();
    EXPECT_EQ(expectedTypeName, actualTypeName);

    return std::any_cast<const EventType*>(anyEvent);
}

void ExpectIsInitialSuspend(
    const auto* event
)
{
    EXPECT_EQ(true, event->is_initial_suspend);
    EXPECT_EQ(false, event->is_co_await);
    EXPECT_EQ(false, event->is_co_yield);
    EXPECT_EQ(false, event->is_final_suspend);
}

void ExpectIsFinalSuspend(
    const auto* event
)
{
    EXPECT_EQ(false, event->is_initial_suspend);
    EXPECT_EQ(false, event->is_co_await);
    EXPECT_EQ(false, event->is_co_yield);
    EXPECT_EQ(true, event->is_final_suspend);
}

#pragma warning (disable: 4702)
ASYNC_TEST_F(tracing_tests, traces_basic_events_of_task)
{
    auto taskLambda = [](
        traced_events_checker& eventsChecker,
        std::string inputArgument
        ) -> test_traced_task<>
    {
        co_return;
    };
    
    int eventIndex = 0;
    test_traced_promise<void>* expectedPromise = nullptr;
    
    using initialSuspendAwaiter = tracing::traced_awaiter<
        trace_sink,
        std::suspend_always,
        tracing::initial_suspend_awaiter
    >;

    initialSuspendAwaiter* expectedInitialSuspendAwaiter = nullptr;
    
    using finalSuspendAwaiter = tracing::traced_awaiter<
        trace_sink,
        detail::final_suspend_transfer,
        tracing::final_suspend_awaiter
    >;

    finalSuspendAwaiter* expectedFinalSuspendAwaiter = nullptr;

    traced_events_checker eventChecker
    {
        [&](this auto& self, const std::any& anyEvent)
        {
            using namespace tracing::events;
            
            ++eventIndex;
            // We do this checkingIndex so that when trace messages are
            // added or removed we don't have to change every index,
            // we just insert code into the right place.
            int checkingIndex = 0;
            if (eventIndex == ++checkingIndex)
            {
                if constexpr (Config::Lambda_Reference_Is_First_Argument_Of_Promise_Constructor)
                {
                    using expectedEventType = create_promise<
                        test_traced_promise<void>,
                        decltype(taskLambda) const&,
                        traced_events_checker&,
                        std::string&
                    >;

                    auto event = CastEventType<expectedEventType>(anyEvent);

                    EXPECT_NE(nullptr, expectedPromise = event->Promise);
                    EXPECT_EQ(&taskLambda, &get<0>(event->Arguments));
                    EXPECT_EQ(&eventChecker, &get<1>(event->Arguments));
                    EXPECT_EQ(std::string("hello"), get<2>(event->Arguments));
                }
                else
                {
                    using expectedEventType = create_promise<
                        test_traced_promise<void>,
                        traced_events_checker&,
                        std::string&
                    >;

                    auto event = CastEventType<expectedEventType>(anyEvent);

                    EXPECT_NE(nullptr, expectedPromise = event->Promise);
                    EXPECT_EQ(&eventChecker, &get<0>(event->Arguments));
                    EXPECT_EQ(std::string("hello"), get<1>(event->Arguments));
                }
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_begin<
                    initialSuspendAwaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_NE(nullptr, expectedInitialSuspendAwaiter = event->Awaiter);
                
                ExpectIsInitialSuspend(event);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_result<
                    initialSuspendAwaiter,
                    bool
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedInitialSuspendAwaiter, event->Awaiter);

                ExpectIsInitialSuspend(event);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
                EXPECT_EQ(false, event->Result);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_begin<
                    initialSuspendAwaiter,
                    std::coroutine_handle<test_traced_promise<void>>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedInitialSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(expectedPromise, &get<0>(event->Arguments).promise());
                ExpectIsInitialSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_result<
                    initialSuspendAwaiter,
                    void,
                    std::coroutine_handle<test_traced_promise<void>>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedInitialSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(expectedPromise, &get<0>(event->Arguments).promise());
                EXPECT_EQ(true, event->is_void_result);
                ExpectIsInitialSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_begin<
                    initialSuspendAwaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedInitialSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
                ExpectIsInitialSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_result<
                    initialSuspendAwaiter,
                    void
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedInitialSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
                EXPECT_EQ(true, event->is_void_result);
                ExpectIsInitialSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = return_void_begin<
                    test_traced_promise<void>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedPromise, event->Promise);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = return_void_result<
                    test_traced_promise<void>,
                    void
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedPromise, event->Promise);
                EXPECT_EQ(true, event->is_void_result);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_begin<
                    finalSuspendAwaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_NE(nullptr, expectedFinalSuspendAwaiter = event->Awaiter);

                ExpectIsFinalSuspend(event);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_result<
                    finalSuspendAwaiter,
                    bool
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedFinalSuspendAwaiter, event->Awaiter);

                ExpectIsFinalSuspend(event);
                EXPECT_EQ(std::tuple<>{}, event->Arguments);
                EXPECT_EQ(false, event->Result);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_begin<
                    finalSuspendAwaiter,
                    std::coroutine_handle<test_traced_promise<void>>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedFinalSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(expectedPromise, &get<0>(event->Arguments).promise());
                ExpectIsFinalSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_result<
                    finalSuspendAwaiter,
                    std::coroutine_handle<void>,
                    std::coroutine_handle<test_traced_promise<void>>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedFinalSuspendAwaiter, event->Awaiter);
                EXPECT_EQ(expectedPromise, &get<0>(event->Arguments).promise());
                EXPECT_EQ(false, event->is_void_result);
                EXPECT_NE(nullptr, event->Result.address());
                ExpectIsFinalSuspend(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = destroy_promise<
                    test_traced_promise<void>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedPromise, event->Promise);
            }
            else
            {
                EXPECT_FALSE(true);
            }
        }
    };

    co_await taskLambda(eventChecker, "hello");
    EXPECT_EQ(14, eventIndex);
}


}