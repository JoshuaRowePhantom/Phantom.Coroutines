#include "async_test.h"
#include <typeindex>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.tracing;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/tracing.h"
#include "Phantom.Coroutines/task.h"
#endif

namespace Phantom::Coroutines
{

struct tracing_tests : testing::Test
{
    //struct comparable_data_base
    //{
    //    virtual const type_info& type() const = 0;
    //    virtual ~comparable_data_base() {}
    //    virtual bool equals(const comparable_data_base& other) const = 0;
    //};

    //template<
    //    typename T
    //>
    //struct comparable_data : comparable_data_base
    //{
    //    const type_info& type() const override
    //    {
    //        return typeid(T);
    //    }

    //    bool equals(
    //        const comparable_data_base& other
    //    ) const override
    //    {
    //        if (type() != other.type())
    //        {
    //            return false;
    //        }
    //        const comparable& otherValue = static_cast<const comparable&>(other);
    //        return value == otherValue.value;
    //    }

    //    T value;
    //};

    //struct exception_holder_type_info {};

    //template<
    //    typename Exception
    //>
    //struct exception_holder
    //{
    //    Exception value;
    //};

    //struct exception_holder_comparable_data_base : comparable_data_base
    //{
    //    const type_info& type() const override
    //    {
    //        return typeid(exception_holder_type_info);
    //    }

    //    virtual bool equals(std::exception_ptr) const = 0;
    //};

    //template<>
    //struct comparable_data<std::exception_ptr> : comparable_data_base
    //{
    //    const type_info& type() const override
    //    {
    //        return typeid(std::exception_ptr);
    //    }

    //    bool equals(
    //        const comparable_data_base& other
    //    ) const override
    //    {
    //        if (other.type() != typeid(exception_holder_type_info))
    //        {
    //            return false;
    //        }
    //        auto& exceptionHolderComparable = static_cast<const exception_holder_comparable_data_base&>(other);
    //        return exceptionHolderComparable.equals(value);
    //    }

    //    comparable_data(std::exception_ptr exception) :
    //        value(exception)
    //    {
    //    }

    //    std::exception_ptr value;
    //};

    //template<
    //    typename Exception
    //>
    //struct comparable_data<exception_holder<Exception>> : exception_holder_comparable_data_base
    //{
    //    bool equals(
    //        std::exception_ptr exception
    //    ) const override
    //    {
    //        try
    //        {
    //            std::rethrow_exception(exception);
    //        }
    //        catch (const Exception& e)
    //        {
    //            return true;
    //        }
    //        catch (...)
    //        {
    //            return false;
    //        }
    //    }

    //    bool equals(
    //        const comparable_data_base& other
    //    ) const override
    //    {
    //        if (other.type() == type())
    //        {
    //            return true;
    //        }
    //        if (other.type() == typeid(std::exception_ptr))
    //        {
    //            return equals(static_cast<const comparable_data<std::exception_ptr>&>(other).value);
    //        }
    //        return false;
    //    }
    //};

    //struct comparable
    //{
    //    std::shared_ptr<comparable_data_base> value;

    //    constexpr comparable() = default;

    //    template<
    //        typename T
    //    >
    //    comparable(
    //        T&& data
    //    ) :
    //        value(std::make_shared<comparable_data<std::remove_cvref_t<T>>>(data))
    //    {
    //    }

    //    friend bool operator==(
    //        const comparable& lhs,
    //        const comparable& rhs
    //        )
    //    {
    //        return 
    //            lhs.value == rhs.value
    //            ||
    //            lhs.value && rhs.value && lhs.value->equals(*rhs.value);
    //    }
    //};

    //static constexpr bool has_promise = true;
    //static constexpr bool no_promise = false;

    //using no_arguments = comparable;
    //using no_result = comparable;

    //struct traced_event
    //{
    //    std::type_index type;
    //    bool has_promise = false;
    //    bool has_awaiter = false;

    //    comparable arguments;
    //    comparable result;
    //    comparable exception;
    //    
    //    template<
    //        typename Event
    //    >
    //    static comparable get_arguments(
    //        const Event& event
    //    )
    //    {
    //        if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_arguments))
    //        {
    //            return comparable(event.arguments);
    //        }
    //        else
    //        {
    //            return comparable{};
    //        }
    //    }

    //    template<
    //        typename Event
    //    >
    //    static comparable get_result(
    //        const Event& event
    //    )
    //    {
    //        if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_result))
    //        {
    //            return comparable(event.result);
    //        }
    //        else
    //        {
    //            return comparable{};
    //        }
    //    }

    //    template<
    //        typename Event
    //    >
    //    static comparable get_exception(
    //        const Event& event
    //    )
    //    {
    //        if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_exception))
    //        {
    //            return comparable(event.exception);
    //        }
    //        else
    //        {
    //            return comparable{};
    //        }
    //    }

    //    template<
    //        typename Event
    //    >
    //    static traced_event from_event(
    //        Event& event
    //    )
    //    {
    //        return traced_event
    //        {
    //            .type = typeid(Event),
    //            .has_promise = tracing::filters::has_promise(event),
    //            .has_awaiter = tracing::filters::has_awaiter(event),
    //            .arguments = get_arguments(event),
    //            .result = get_result(event),
    //            .exception = get_exception(event),
    //        };
    //    }

    //    friend auto operator<=>(const traced_event&, const traced_event&) = default;
    //};

    struct traced_event
    {
        std::any event;
        //std::type_index type;
        //std::any promise;
        //std::any awaiter;
        //std::any arguments;
        //std::any result;
        //std::exception_ptr exception;

        static traced_event from_event(
            const auto& event
        )
        {
            return { &event };
        }

        //static traced_event from_event(
        //    const auto& event
        //)
        //{
        //    traced_event tracedEvent
        //    {
        //        .type = typeid(event),
        //    };

        //    if constexpr (tracing::filters::check_constexpr<decltype(event)>(tracing::filters::has_promise))
        //    {
        //        tracedEvent.promise = event.promise;
        //    }
        //    if constexpr (tracing::filters::check_constexpr<decltype(event)>(tracing::filters::has_awaiter))
        //    {
        //        tracedEvent.awaiter = event.awaiter;
        //    }
        //    if constexpr (tracing::filters::check_constexpr<decltype(event)>(tracing::filters::has_arguments))
        //    {
        //        tracedEvent.arguments = &event.arguments;
        //    }
        //    if constexpr (tracing::filters::check_constexpr<decltype(event)>(tracing::filters::has_result))
        //    {
        //        tracedEvent.result = &event.result;
        //    }
        //    if constexpr (tracing::filters::check_constexpr<decltype(event)>(tracing::filters::has_exception))
        //    {
        //        tracedEvent.exception = event.exception;
        //    }

        //    return tracedEvent;
        //}
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
#if PHANTOM_COROUTINES_LAMBDA_REFERENCE_IS_FIRST_ARGUMENT
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
#else
                using expectedEventType = create_promise<
                    test_traced_promise<void>,
                    traced_events_checker&,
                    std::string&
                >;

                auto event = CastEventType<expectedEventType>(anyEvent);

                EXPECT_NE(nullptr, expectedPromise = event->Promise);
                EXPECT_EQ(&eventChecker, &get<0>(event->Arguments));
                EXPECT_EQ(std::string("hello"), get<1>(event->Arguments));
#endif
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