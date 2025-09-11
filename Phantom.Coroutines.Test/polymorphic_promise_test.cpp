#include <concepts>
#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.polymorphic_promise;
import Phantom.Coroutines.task;
import Phantom.Coroutines.value_awaiter;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/await_all_await_transform.h"
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/polymorphic_promise.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/value_awaiter.h"
#endif

namespace Phantom::Coroutines
{
namespace
{

struct polymorphic_promise_tests : testing::Test
{
    struct get_name {};

    template<
        template<typename> typename PromiseTemplate
    >
    struct test_promise_specifier
    {
    };

    template<
        typename BasePromise
    >
    struct test_promise_base
        : polymorphic_promise<
        BasePromise
        >
    {
        virtual std::string get_name() const
        {
            return "test_promise_base";
        }

        auto await_transform(
            struct get_name
        )
        {
            return value_awaiter<std::string>{ get_name() };
        }
    };

    template<
        typename BasePromise
    >
    struct test_promise_derived_1
        : polymorphic_promise<
        test_promise_base<BasePromise>
        >
    {
        std::string get_name() const override
        {
            return "test_promise_derived_1";
        }
    };

    template<
        typename BasePromise
    >
    struct test_promise_derived_2
        : polymorphic_promise<
        test_promise_base<BasePromise>
        >
    {
        std::string get_name() const override
        {
            return "test_promise_derived_2";
        }
    };

    template<
        typename Result = void
    >
    using test_task = basic_task<
        test_promise_base<
            task_promise<Result>
        >
    >;
};
}
}

namespace std
{
template<
    typename Result,
    typename This,
    template <typename> typename PromiseTemplate
>
struct coroutine_traits<
    ::Phantom::Coroutines::polymorphic_promise_tests::test_task<Result>,
    This,
    ::Phantom::Coroutines::polymorphic_promise_tests::test_promise_specifier<PromiseTemplate>
>
{
    using promise_type = PromiseTemplate<
        typename ::Phantom::Coroutines::polymorphic_promise_tests::test_task<Result>::promise_type
    >;
};
}

namespace Phantom::Coroutines
{
ASYNC_TEST_F(polymorphic_promise_tests, can_invoke_virtual_methods)
{
    auto lambda = [](auto) -> test_task<std::string>
    {
        co_return co_await get_name();
    };

    auto derived1Result = co_await lambda(test_promise_specifier<test_promise_derived_1>{});
    auto derived2Result = co_await lambda(test_promise_specifier<test_promise_derived_2>{});

    EXPECT_EQ("test_promise_derived_1", derived1Result);
    EXPECT_EQ("test_promise_derived_2", derived2Result);
}

}
