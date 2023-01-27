#include "../Phantom.Coroutines.Test/async_test.h"
#include "cppcoro/cancellation_source.hpp"

namespace cppcoro
{

TEST(cppcoro_cancellation_source_test, can_be_cancelled_starts_true)
{
    cancellation_source source;
    ASSERT_TRUE(source.can_be_cancelled());
}

TEST(cppcoro_cancellation_source_test, cancellation_token_is_cancelled_if_source_is_requested)
{
    cancellation_source source;
    cancellation_token token = source.token();
    ASSERT_FALSE(source.is_cancellation_requested());
    ASSERT_FALSE(token.is_cancellation_requested());
    source.request_cancellation();
    ASSERT_TRUE(source.is_cancellation_requested());
    ASSERT_TRUE(token.is_cancellation_requested());
}

TEST(cppcoro_cancellation_source_test, cancellation_token_throw_if_cancellation_requested_throws_operation_cancelled_exception)
{
    cancellation_source source;
    cancellation_token token = source.token();
    token.throw_if_cancellation_requested(),
    source.request_cancellation();
    ASSERT_THROW(
        token.throw_if_cancellation_requested(),
        operation_cancelled
    );
}

}