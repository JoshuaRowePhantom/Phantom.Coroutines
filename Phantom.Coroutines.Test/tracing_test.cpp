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
    struct comparable_data_base
    {
        virtual const type_info& type() const = 0;
        virtual ~comparable_data_base() {}
        virtual bool equals(const comparable_data_base& other) const = 0;
    };

    template<
        typename T
    >
    struct comparable_data : comparable_data_base
    {
        const type_info& type() const override
        {
            return typeid(T);
        }

        bool equals(
            const comparable_data_base& other
        ) const override
        {
            if (type() != other.type())
            {
                return false;
            }
            const comparable& otherValue = static_cast<const comparable&>(other);
            return value == otherValue.value;
        }

        T value;
    };

    struct exception_holder_type_info {};

    template<
        typename Exception
    >
    struct exception_holder
    {
        Exception value;
    };

    struct exception_holder_comparable_data_base : comparable_data_base
    {
        const type_info& type() const override
        {
            return typeid(exception_holder_type_info);
        }

        virtual bool equals(std::exception_ptr) const = 0;
    };

    template<>
    struct comparable_data<std::exception_ptr> : comparable_data_base
    {
        const type_info& type() const override
        {
            return typeid(std::exception_ptr);
        }

        bool equals(
            const comparable_data_base& other
        ) const override
        {
            if (other.type() != typeid(exception_holder_type_info))
            {
                return false;
            }
            auto& exceptionHolderComparable = static_cast<const exception_holder_comparable_data_base&>(other);
            return exceptionHolderComparable.equals(value);
        }

        comparable_data(std::exception_ptr exception) :
            value(exception)
        {
        }

        std::exception_ptr value;
    };

    template<
        typename Exception
    >
    struct comparable_data<exception_holder<Exception>> : exception_holder_comparable_data_base
    {
        bool equals(
            std::exception_ptr exception
        ) const override
        {
            try
            {
                std::rethrow_exception(exception);
            }
            catch (const Exception& e)
            {
                return true;
            }
            catch (...)
            {
                return false;
            }
        }

        bool equals(
            const comparable_data_base& other
        ) const override
        {
            if (other.type() == type())
            {
                return true;
            }
            if (other.type() == typeid(std::exception_ptr))
            {
                return equals(static_cast<const comparable_data<std::exception_ptr>&>(other).value);
            }
            return false;
        }
    };

    struct comparable
    {
        std::shared_ptr<comparable_data_base> value;

        constexpr comparable() = default;

        template<
            typename T
        >
        comparable(
            T&& data
        ) :
            value(std::make_shared<comparable_data<std::remove_cvref_t<T>>>(data))
        {
        }

        friend bool operator==(
            const comparable& lhs,
            const comparable& rhs
            )
        {
            return 
                lhs.value == rhs.value
                ||
                lhs.value && rhs.value && lhs.value->equals(*rhs.value);
        }
    };

    static constexpr bool has_promise = true;
    static constexpr bool no_promise = false;

    using no_arguments = comparable;
    using no_result = comparable;

    struct traced_event
    {
        std::type_index type;
        bool has_promise = false;
        bool has_awaiter = false;

        comparable arguments;
        comparable result;
        comparable exception;
        
        template<
            typename Event
        >
        static comparable get_arguments(
            const Event& event
        )
        {
            if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_arguments))
            {
                return comparable(event.arguments);
            }
            else
            {
                return comparable{};
            }
        }

        template<
            typename Event
        >
        static comparable get_result(
            const Event& event
        )
        {
            if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_result))
            {
                return comparable(event.result);
            }
            else
            {
                return comparable{};
            }
        }

        template<
            typename Event
        >
        static comparable get_exception(
            const Event& event
        )
        {
            if constexpr (tracing::filters::check_constexpr<Event>(tracing::filters::has_exception))
            {
                return comparable(event.exception);
            }
            else
            {
                return comparable{};
            }
        }

        template<
            typename Event
        >
        static traced_event from_event(
            Event& event
        )
        {
            return traced_event
            {
                .type = typeid(Event),
                .has_promise = tracing::filters::has_promise(event),
                .has_awaiter = tracing::filters::has_awaiter(event),
                .arguments = get_arguments(event),
                .result = get_result(event),
                .exception = get_exception(event),
            };
        }

        friend auto operator<=>(const traced_event&, const traced_event&) = default;
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
                traced_event::from_event(traceEvent));
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

#pragma warning (disable: 4702)
ASYNC_TEST_F(tracing_tests, traces_basic_events_of_task)
{
    traced_events events;

    auto taskLambda = [](
        traced_events& events, 
        std::string inputArgument
        ) -> test_traced_task<>
    {
        EXPECT_EQ(7, events.m_traceEvents.size());
        co_return;
    };

    co_await taskLambda(events, "hello");
    EXPECT_EQ(14, events.m_traceEvents.size());

    auto& expectedCreateEventType = typeid(tracing::events::create_promise<
        test_traced_promise<void>,
        decltype(taskLambda) const &,
        traced_events&,
        std::string&
    >);

    EXPECT_EQ(
        (traced_event
        {
            .type = expectedCreateEventType,
            .has_promise = has_promise,
        }),
        events.m_traceEvents[0]);
}


}