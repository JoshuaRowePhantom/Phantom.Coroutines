#include <gtest/gtest.h>
#include "awaiters.h"
#include "Phantom.Coroutines/awaiter_wrapper.h"

namespace Phantom::Coroutines::detail
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

}