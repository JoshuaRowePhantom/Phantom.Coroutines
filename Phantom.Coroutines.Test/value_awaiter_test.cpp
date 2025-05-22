#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.value_awaiter;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/value_awaiter.h"
#endif

namespace Phantom::Coroutines
{

ASYNC_TEST(value_awaiter_test, can_await_by_value)
{
    value_awaiter<std::string> awaiter{ "hello" };
    decltype(auto) result = co_await awaiter;
    static_assert(std::same_as<decltype(result), std::string>);
    EXPECT_EQ("hello", result);
}

ASYNC_TEST(value_awaiter_test, can_await_by_reference)
{
    std::string expected = "hello";
    value_awaiter<std::string&> awaiter{ expected };
    decltype(auto) result = co_await awaiter;
    static_assert(std::same_as<decltype(result), std::string&>);
    EXPECT_EQ(&expected, &result);
}

}