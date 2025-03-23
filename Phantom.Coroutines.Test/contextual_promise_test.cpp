#include "async_test.h"
#include <variant>
#include <vector>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.async_manual_reset_event;
import Phantom.Coroutines.async_scope;
import Phantom.Coroutines.contextual_promise;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/async_manual_reset_event.h"
#include "Phantom.Coroutines/async_scope.h"
#include "Phantom.Coroutines/contextual_promise.h"
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/task.h"
#endif

namespace Phantom::Coroutines::Test
{
namespace 
{

enum class operation_type
{
    enter,
    leave,
    suspend,
    resume
};

struct operation
{
    operation_type m_type;
    auto operator<=>(const operation&) const = default;
};

typedef std::vector<
    operation
> operations_vector;
}

template<
    typename BasePromise
> class test_contextual_promise
    :
    public contextual_promise<BasePromise>
{
public:
    template<is_awaitable Awaiter>
    struct test_contextual_promise_awaiter : 
        public awaiter_wrapper<Awaiter>,
        public extensible_promise_handle<test_contextual_promise>
    {
        test_contextual_promise_awaiter(
            test_contextual_promise& promise,
            auto&& awaiterFunction
        ) : awaiter_wrapper<Awaiter> { std::forward<decltype(awaiterFunction)>(awaiterFunction) },
            extensible_promise_handle<test_contextual_promise> { promise }
        {
        }

        decltype(auto) promise()
        {
            return this->test_contextual_promise_awaiter::extensible_promise_handle::promise();
        }

        auto await_ready() noexcept
        {
            return this->awaiter().await_ready();
        }

        auto await_suspend(
            auto&&... args
        ) noexcept
        {
            this->promise().m_operations.push_back(
                { operation_type::suspend }
            );
            return this->awaiter().await_suspend(
                std::forward<decltype(args)>(args)...);
        }

        auto await_resume() noexcept(noexcept(this->awaiter().await_resume()))
        {
            this->promise().m_operations.push_back(
                { operation_type::resume }
            );
            return this->awaiter().await_resume();
        }
    };

    template<
        std::invocable AwaiterFunc
    > test_contextual_promise_awaiter(
        test_contextual_promise&, 
        AwaiterFunc
    ) -> test_contextual_promise_awaiter<std::invoke_result_t<AwaiterFunc>>;

    test_contextual_promise(
        auto&&,
        operations_vector& operations
    ) : m_operations { operations }
    {}

    operations_vector& m_operations;

    void enter()
    {
        m_operations.push_back(
            { operation_type::enter });
    }

    void leave()
    {
        m_operations.push_back(
            { operation_type::leave });
    }

    auto initial_suspend()
    {
        auto lambda = [&]() { return this->test_contextual_promise::contextual_promise::initial_suspend(); };
        static_assert(is_awaiter<decltype(lambda())>);
        return test_contextual_promise_awaiter
        { 
            *this,
            lambda,
        };
    }

    auto await_transform(
        auto&& awaitable
    )
    {
        return test_contextual_promise_awaiter
        {
            *this,
            [&]() -> decltype(auto) 
            {
                return this->contextual_promise<BasePromise>::await_transform(
                    std::forward<decltype(awaitable)>(awaitable));
            }
        };
    }

    auto final_suspend() noexcept
    {
        return test_contextual_promise_awaiter
        {
            *this,
            [&]() noexcept { return this->test_contextual_promise::contextual_promise::final_suspend(); }
        };
    }
};

template<
    typename T = void
> using test_contextual_task = basic_task<
    test_contextual_promise<task_promise<T>>>;

static_assert(is_awaiter<test_contextual_task<>::promise_type::test_contextual_promise_awaiter<async_manual_reset_event<>>>);
static_assert(noexcept(std::declval<test_contextual_task<>::promise_type>().final_suspend()));
static_assert(noexcept(std::declval<test_contextual_task<>::promise_type>().final_suspend().await_ready()));
static_assert(noexcept(std::declval<test_contextual_task<>::promise_type>().final_suspend().await_suspend(coroutine_handle<>(nullptr))));
static_assert(noexcept(std::declval<test_contextual_task<>::promise_type>().final_suspend().await_resume()));

ASYNC_TEST(contextual_promise_test, context_enter_on_initial_suspend_leave_on_final_suspend)
{
    operations_vector operations;
    async_manual_reset_event<> event;

    auto taskLambda = [&](auto&) -> test_contextual_task<>
    {
        co_await event;
    };

    auto task = taskLambda(operations);

    EXPECT_EQ(
        operations,
        (operations_vector
        {
            { operation_type::suspend },
        }));

    async_scope<> scope;
    scope.spawn(std::move(task));

    EXPECT_EQ(
        operations,
        (operations_vector
        {
            // initial_suspend suspend
            { operation_type::suspend },
            // initial_suspend resume
            { operation_type::resume },
            { operation_type::enter },
            // asyncAutoResetEvent suspend
            { operation_type::suspend },
            { operation_type::leave },
        }));

    event.set();

    EXPECT_EQ(
        operations,
        (operations_vector
        {
            // initial_suspend suspend
            { operation_type::suspend },
            // initial_suspend resume
            { operation_type::resume },
            { operation_type::enter },
            // asyncAutoResetEvent suspend
            { operation_type::suspend },
            { operation_type::leave },
            // asyncAutoResetEvent resume
            { operation_type::resume },
            { operation_type::enter },
            // final_suspend suspend
            { operation_type::suspend },
            { operation_type::leave },
        }));

    co_await scope.join();
}


}
