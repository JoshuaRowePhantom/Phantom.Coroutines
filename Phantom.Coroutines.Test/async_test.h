#include <gtest/gtest.h>
#include "Phantom.Coroutines/sync_wait.h"
#include "Phantom.Coroutines/task.h"

#define ASYNC_TEST_CLASS_NAME(test_suite_name, test_name) test_suite_name ## _ ## test_name ## _AsyncTest

#define ASYNC_TEST_(test_suite_name, test_name, parent_class, parent_id) \
class ASYNC_TEST_CLASS_NAME(test_suite_name, test_name) \
    : public parent_class \
{ \
public: \
    ::Phantom::Coroutines::task<> AsyncTestBody(); \
}; \
\
GTEST_TEST_(test_suite_name, test_name, ASYNC_TEST_CLASS_NAME(test_suite_name, test_name), ::testing::internal::GetTestTypeId()) \
{ \
    sync_wait(AsyncTestBody()); \
} \
\
::Phantom::Coroutines::task<> ASYNC_TEST_CLASS_NAME(test_suite_name, test_name)::AsyncTestBody()

#define ASYNC_TEST(test_suite_name, test_name) ASYNC_TEST_(test_suite_name, test_name, ::testing::Test, ::testing::internal::GetTestTypeId())
#define ASYNC_TEST_F(test_suite_name, test_name) ASYNC_TEST_(test_suite_name, test_name, test_fixture, ::testing::internal::GetTypeId<test_fixture>())

