#include <gtest/gtest.h>
#include "awaiters.h"
#include "Phantom.Coroutines/detail/awaiter_wrapper.h"

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
	using awaiter_wrapper_test_awaiter::awaiter_wrapper::get_awaiter;
};

TEST(awaiter_wrapper_test, can_wrap_awaiter_value)
{
	generic_awaiter<void, void> awaiter;
	awaiter_wrapper_test_awaiter<generic_awaiter<void, void>> wrapper = std::move(awaiter);
	ASSERT_NE(&wrapper.get_awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_lvalue)
{
	generic_awaiter<void, void> awaiter;
	awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&> wrapper = awaiter;
	ASSERT_EQ(&wrapper.get_awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaiter_rvalue)
{
	generic_awaiter<void, void> awaiter;
	awaiter_wrapper_test_awaiter<generic_awaiter<void, void>&&> wrapper = std::move(awaiter);
	ASSERT_EQ(&wrapper.get_awaiter(), &awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_value)
{
	generic_awaitable_value<void, void> awaitable;
	awaiter_wrapper_test_awaiter<generic_awaitable_rvalue<void, void>> wrapper = std::move(awaitable);
	ASSERT_NE(&wrapper.get_awaiter(), &awaitable.m_awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_lvalue)
{
	generic_awaitable_lvalue<void, void> awaitable;
	awaiter_wrapper_test_awaiter<generic_awaitable_lvalue<void, void>&> wrapper = awaitable;
	ASSERT_EQ(&wrapper.get_awaiter(), &awaitable.m_awaiter);
}

TEST(awaiter_wrapper_test, can_wrap_awaitable_rvalue)
{
	generic_awaitable_rvalue<void, void> awaitable;
	awaiter_wrapper_test_awaiter<generic_awaitable_rvalue<void, void>> wrapper = std::move(awaitable);
	ASSERT_EQ(&wrapper.get_awaiter(), &awaitable.m_awaiter);
}

}