#include "async_test.h"
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
    struct traced_event_data_base
    {
        virtual const type_info& type() = 0;
        virtual ~traced_event_data_base() {}
        virtual tracing::events::event& value() = 0;
    };

    template<
        std::derived_from<tracing::events::event> T
    >
    struct traced_event_data : traced_event_data_base
    {
        const type_info& type() override
        {
            return typeid(T);
        }

        tracing::events::event& value() override
        {
            return storedValue;
        }
        
        T storedValue;

        traced_event_data(
            T value
        ) : 
            storedValue{ value }
        { }
    };

    struct traced_event
    {
        std::shared_ptr<traced_event_data_base> value;

        traced_event(
            std::derived_from<tracing::events::event> auto event
        ) :
            value(std::make_shared<traced_event_data<decltype(event)>>(event))
        {
        }

        template<
            std::derived_from<tracing::events::event> Event
        >
        bool operator==(const Event& event)
        {
            if (value->type() != typeid(Event))
            {
                return false;
            }

            Event& thisEvent = static_cast<Event>(value->value());
            return thisEvent == event;
        }
    };

    struct traced_events
    {
        std::vector<traced_event> m_traceEvents;
    };

    struct trace_sink
    {
        traced_events& events;

        trace_sink(
            auto&... args
        ) :
            events(get<traced_events&>(std::tie(args...)))
        { }

        void operator()(const auto& traceEvent)
        {
            events.m_traceEvents.push_back(
                traced_event{ traceEvent });
        }
    };

    template<
        typename T
    >
    using test_traced_promise = tracing::traced_promise<
        trace_sink,
        task_promise<T>>;

    template<
        typename T = void
    >
    using test_traced_task = basic_task<test_traced_promise<T>>;
};

#pragma warning (disable: 4702)
ASYNC_TEST_F(tracing_tests, traces_basic_events_of_task)
{
    traced_events events;

    auto taskLambda = [](traced_events& events, std::string inputArgument) -> test_traced_task<>
    {
        EXPECT_EQ(7, events.m_traceEvents.size());
        co_return;
    };

    co_await taskLambda(events, "hello");
    EXPECT_EQ(14, events.m_traceEvents.size());
}


}