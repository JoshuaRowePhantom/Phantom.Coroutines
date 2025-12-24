#include <functional>
#include "Phantom.Coroutines/detail/config_macros.h"
#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.value_awaiter;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/value_awaiter.h"
#include "lifetime_tracker.h"
#endif

namespace Phantom::Coroutines
{

ASYNC_TEST(value_awaiter_test, await_value_from_lvalue_returns_const_reference)
{
    lifetime_statistics lifetimeStatistics;
    value_awaiter awaiter{ lifetimeStatistics.tracker() };
    decltype(auto) result = co_await awaiter;
    static_assert(std::same_as<decltype(result), const lifetime_tracker&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

ASYNC_TEST(value_awaiter_test, await_value_from_rvalue_returns_rvalue_reference)
{
    lifetime_statistics lifetimeStatistics;
    value_awaiter awaiter{ lifetimeStatistics.tracker() };
#if PHANTOM_COROUTINES_MSVC_INCORRECTLY_COPIES_CO_AWAIT_RVALUE_REFERENCE
    // The extra "move" is to workaround a compiler bug in MSVC where it copies the result of await_resume.
    decltype(auto) result = std::move(co_await std::move(awaiter));
#else
    decltype(auto) result = co_await awaiter;
#endif
    static_assert(std::same_as<decltype(result), lifetime_tracker&&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

ASYNC_TEST(value_awaiter_test, await_lvalue_reference_from_lvalue_returns_lvalue_reference)
{
    lifetime_statistics lifetimeStatistics;
    lifetime_tracker tracker = lifetimeStatistics.tracker();
    value_awaiter<lifetime_tracker&> awaiter{ tracker };
    decltype(auto) result = co_await awaiter;
    static_assert(std::same_as<decltype(result), lifetime_tracker&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

ASYNC_TEST(value_awaiter_test, await_lvalue_reference_from_rvalue_returns_lvalue_reference)
{
    lifetime_statistics lifetimeStatistics;
    lifetime_tracker tracker = lifetimeStatistics.tracker();
    value_awaiter<lifetime_tracker&> awaiter{ tracker };
    decltype(auto) result = co_await std::move(awaiter);
    static_assert(std::same_as<decltype(result), lifetime_tracker&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

ASYNC_TEST(value_awaiter_test, await_rvalue_reference_from_lvalue_returns_rvalue_reference)
{
    lifetime_statistics lifetimeStatistics;
    lifetime_tracker tracker = lifetimeStatistics.tracker();
    value_awaiter<lifetime_tracker&&> awaiter{ std::move(tracker) };
#if PHANTOM_COROUTINES_MSVC_INCORRECTLY_COPIES_CO_AWAIT_RVALUE_REFERENCE
    // The extra "move" is to workaround a compiler bug in MSVC where it copies the result of await_resume.
    decltype(auto) result = std::move(co_await awaiter);
#else
    decltype(auto) result = co_await awaiter;
#endif
    static_assert(std::same_as<decltype(result), lifetime_tracker&&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

ASYNC_TEST(value_awaiter_test, await_rvalue_reference_from_rvalue_returns_rvalue_reference)
{
    lifetime_statistics lifetimeStatistics;
    lifetime_tracker tracker = lifetimeStatistics.tracker();
    value_awaiter<lifetime_tracker&&> awaiter{ std::move(tracker) };
#if PHANTOM_COROUTINES_MSVC_INCORRECTLY_COPIES_CO_AWAIT_RVALUE_REFERENCE
    // The extra "move" is to workaround a compiler bug in MSVC where it copies the result of await_resume.
    decltype(auto) result = std::move(co_await awaiter);
#else
    decltype(auto) result = co_await awaiter;
#endif
    static_assert(std::same_as<decltype(result), lifetime_tracker&&>);
    EXPECT_EQ(0, lifetimeStatistics.copy_construction_count);
    EXPECT_EQ(0, lifetimeStatistics.move_construction_count);
    EXPECT_EQ(lifetimeStatistics, result);
    EXPECT_EQ(std::addressof(awaiter.m_value), std::addressof(result));
}

}