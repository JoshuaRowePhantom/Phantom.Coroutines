#include "async_test.h"
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
        traced_events_checker& checker;
        
        trace_sink(
            trace_sink& other
        ) : checker{ other.checker }
        { }
        
        trace_sink(
            const trace_sink& other
        ) : checker{ other.checker }
        { }

        trace_sink(
            auto&... args
        ) :
            checker(get<traced_events_checker&>(std::tie(args...)))
        {

        }

        void operator()(const auto& traceEvent)
        {
            if (Filter{}(traceEvent))
            {
                checker(&traceEvent);
            }
        }
    };

    template<
        typename Result,
        typename Filter
    >
    using test_traced_promise = traced_promise<
        trace_sink<Filter>,
        polymorphic_promise<task_promise<Result>>
    >;

    template<
        typename T = void
    >
    using test_traced_task = basic_task<polymorphic_promise<task_promise<T>>>;

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

ASYNC_TEST_F(tracing_tests, traces_basic_events_of_task)
{
    PHANTOM_COROUTINES_MSVC_PUSH_DISABLE_WARNING(4702)
    auto taskLambda = [](
        traced_events_checker& eventsChecker,
        std::string inputArgument
        ) -> test_traced_task<>
    {
        co_return;
    };
    PHANTOM_COROUTINES_MSVC_POP_WARNINGS()

    using expected_promise_type = coroutine_function_traits<decltype(&decltype(taskLambda)::operator())>::promise_type;
    expected_promise_type* expectedPromise = nullptr;
    
    using initialSuspendAwaiter = traced_awaiter<
        trace_sink<filters::any_event_fn>,
        std::suspend_always,
        initial_suspend_awaiter
    >;

    initialSuspendAwaiter* expectedInitialSuspendAwaiter = nullptr;
    
    using finalSuspendAwaiter = traced_awaiter<
        trace_sink<filters::any_event_fn>,
        final_suspend_transfer,
        final_suspend_awaiter
    >;

    finalSuspendAwaiter* expectedFinalSuspendAwaiter = nullptr;

    int eventIndex = 0;
    traced_events_checker eventChecker
    {
        [&](const std::any& anyEvent)
        {
            using namespace events;
            
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
                        expected_promise_type,
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
                        expected_promise_type,
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
                    std::coroutine_handle<expected_promise_type>
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
                    std::coroutine_handle<expected_promise_type>
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
                    expected_promise_type
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedPromise, event->Promise);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = return_void_result<
                    expected_promise_type,
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
                    std::coroutine_handle<expected_promise_type>
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
                    std::coroutine_handle<expected_promise_type>
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
                    expected_promise_type
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

ASYNC_TEST_F(tracing_tests, traces_co_await_events_await_ready_true_void_result)
{
    using awaiter_type = Coroutines::detail::suspend_never;

    auto taskLambda = [](
        traced_events_checker& eventsChecker,
        std::string inputArgument,
        filters::is_co_await_fn = {}
        ) -> test_traced_task<>
    {
        co_await awaiter_type{};
    };

    using traced_awaiter = traced_awaiter<
        trace_sink<filters::is_co_await_fn>,
        awaiter_type,
        co_await_awaiter
    >;

    traced_awaiter* expectedAwaiter = nullptr;

    int eventIndex = 0;
    traced_events_checker eventChecker
    {
        [&](const std::any& anyEvent)
        {
            using namespace events;

            ++eventIndex;
            // We do this checkingIndex so that when trace messages are
            // added or removed we don't have to change every index,
            // we just insert code into the right place.
            int checkingIndex = 0;
            if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_begin<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                expectedAwaiter = event->Awaiter;
                EXPECT_EQ(false, filters::has_result(*event).value);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_result<
                    traced_awaiter,
                    bool
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(true, event->Result);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_begin<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_result<
                    traced_awaiter,
                    void
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(true, event->is_void_result);
                ExpectIsCoAwait(event);
            }
            else
            {
                EXPECT_FALSE(true);
            }
        }
    };

    co_await taskLambda(eventChecker, "hello");
    EXPECT_EQ(4, eventIndex);
}

ASYNC_TEST_F(tracing_tests, traces_co_await_events_await_ready_exception)
{
    auto awaiter = test_awaiter()
        .with_await_ready_exception(std::runtime_error("await_ready_exception"));

    using awaiter_type = decltype(awaiter);

    auto taskLambda = [&](
        traced_events_checker& eventsChecker,
        std::string inputArgument,
        filters::is_co_await_fn = {}
        ) -> test_traced_task<>
    {
        co_await awaiter;
    };

    using traced_awaiter = traced_awaiter<
        trace_sink<filters::is_co_await_fn>,
        awaiter_type,
        co_await_awaiter
    >;

    traced_awaiter* expectedAwaiter = nullptr;

    int eventIndex = 0;
    traced_events_checker eventChecker
    {
        [&](const std::any& anyEvent)
        {
            using namespace events;

            ++eventIndex;
            // We do this checkingIndex so that when trace messages are
            // added or removed we don't have to change every index,
            // we just insert code into the right place.
            int checkingIndex = 0;
            if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_begin<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                expectedAwaiter = event->Awaiter;
                EXPECT_EQ(false, filters::has_result(*event).value);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_exception<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_THROW(std::rethrow_exception(event->Exception), std::runtime_error);
                ExpectIsCoAwait(event);
            }
            else
            {
                EXPECT_FALSE(true);
            }
        }
    };

    co_await expect_exception<std::runtime_error>(taskLambda(eventChecker, "hello"));
    EXPECT_EQ(2, eventIndex);
}

ASYNC_TEST_F(tracing_tests, traces_co_await_events_await_suspend_void_result)
{
    auto awaiter = test_awaiter()
        .with_await_ready_false()
        .with_await_suspend_void()
        .with_await_resume_void();

    using awaiter_type = decltype(awaiter);

    auto taskLambda = [&](
        traced_events_checker& eventsChecker,
        std::string inputArgument,
        filters::is_co_await_fn = {}
        ) -> test_traced_task<>
    {
        co_await awaiter;
    };

    using expected_promise_type = coroutine_function_traits<decltype(&decltype(taskLambda)::operator())>::promise_type;

    using traced_awaiter = traced_awaiter<
        trace_sink<filters::is_co_await_fn>,
        awaiter_type,
        co_await_awaiter
    >;

    traced_awaiter* expectedAwaiter = nullptr;

    int eventIndex = 0;
    traced_events_checker eventChecker
    {
        [&](const std::any& anyEvent)
        {
            using namespace events;

            ++eventIndex;
            // We do this checkingIndex so that when trace messages are
            // added or removed we don't have to change every index,
            // we just insert code into the right place.
            int checkingIndex = 0;
            if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_begin<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                expectedAwaiter = event->Awaiter;
                EXPECT_EQ(false, filters::has_result(*event).value);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_ready_result<
                    traced_awaiter,
                    bool
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(false, event->Result);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_begin<
                    traced_awaiter,
                    std::coroutine_handle<expected_promise_type>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(true, static_cast<bool>(get<0>(event->Arguments)));
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_begin<
                    traced_awaiter
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_resume_result<
                    traced_awaiter,
                    void
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(true, event->is_void_result);
                ExpectIsCoAwait(event);
            }
            else if (eventIndex == ++checkingIndex)
            {
                using expectedEventType = await_suspend_result<
                    traced_awaiter,
                    void,
                    std::coroutine_handle<expected_promise_type>
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_EQ(expectedAwaiter, event->Awaiter);
                EXPECT_EQ(true, event->is_void_result);
                ExpectIsCoAwait(event);
            }
            else
            {
                EXPECT_FALSE(true);
            }
        }
    };

    sync_wait(taskLambda(eventChecker, "hello"));
    EXPECT_EQ(6, eventIndex);
    co_return;
}

}
