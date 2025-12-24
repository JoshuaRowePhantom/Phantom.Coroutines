#include <gtest/gtest.h>
#include "awaiters.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.awaiter_wrapper;
#elif defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/awaiter_wrapper.h"
#endif

namespace Phantom::Coroutines
{

template<
    typename Awaiter
> struct awaiter_wrapper_test_awaiter
    :
    public awaiter_wrapper<Awaiter>
{
public:
    using awaiter_wrapper_test_awaiter::awaiter_wrapper::awaiter_wrapper;
    using awaiter_wrapper_test_awaiter::awaiter_wrapper::awaiter;
};

TEST(awaiter_wrapper_test, can_wrap_awaiter_value)
{
    generic_awaiter<void, void> awaiter;
    awaiter_wrapper_test_awaiter<generic_awaiter<void, void>> wrapper{ [&]() { return awaiter; } };
    ASSERT_NE(&wrapper.awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_lvalue)
{
    generic_awaiter<void, void> awaiter;
    awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&> wrapper{ [&]() -> auto& { return awaiter; } };
    ASSERT_EQ(&wrapper.awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_rvalue)
{
    generic_awaiter<void, void> awaiter;
    awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&&> wrapper{ [&]() -> auto&& { return std::move(awaiter); } };
    ASSERT_EQ(&wrapper.awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_lvalue_from_lambda)
{
    generic_awaiter<void, void> awaiter;
    awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&> wrapper{ [&]() -> auto& { return awaiter; } };
    ASSERT_EQ(&wrapper.awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_rvalue_from_lambda)
{
    generic_awaiter<void, void> awaiter;
    awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&&> wrapper{ [&]() -> auto&& { return std::move(awaiter); } };
    ASSERT_EQ(&wrapper.awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_value)
{
    awaiter_wrapper_test_awaiter<generic_awaitable_value<void, void>> wrapper{ [&]() { return generic_awaitable_value<void, void>{}; } };
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_lvalue)
{
    generic_awaitable_lvalue<void, void> awaitable;
    awaiter_wrapper_test_awaiter<generic_awaitable_lvalue<void, void>&> wrapper{ [&]() -> auto& { return awaitable; } };
    ASSERT_EQ(&wrapper.awaiter(), &awaitable.m_awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_rvalue)
{
    generic_awaitable_rvalue<void, void> awaitable;
    awaiter_wrapper_test_awaiter<generic_awaitable_rvalue<void, void>&&> wrapper{ [&]() -> auto&& { return std::move(awaitable); } };
    ASSERT_EQ(&wrapper.awaiter(), &awaitable.m_awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_with_co_await)
{
    // This class is both an awaitable and an awaiter.
    // We check that the awaiter_wrapper picks the awaiter returned by co_await.
    struct test_awaiter_with_co_await : generic_awaiter<void, void>
    {
        generic_awaiter<bool, int> m_awaiter;

        auto& operator co_await()
        {
            return m_awaiter;
        }
    } awaitable;

    awaiter_wrapper_test_awaiter<test_awaiter_with_co_await&&> wrapper{ [&]() -> auto&& { return std::move(awaitable); } };
    ASSERT_EQ(&wrapper.awaiter(), &awaitable.m_awaiter);
}

}