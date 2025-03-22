#ifndef PHANTOM_COROUTINES_INCLUDE_ASYNC_TEST_H_H
#define PHANTOM_COROUTINES_INCLUDE_ASYNC_TEST_H_H

#include <gtest/gtest.h>
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.reusable_task;
#else
#include "Phantom.Coroutines/reusable_task.h"
#endif

namespace Phantom::Coroutines::Test
{
void ExecuteTest(
    ::Phantom::Coroutines::reusable_task<> testTask
);
}

#define ASYNC_TEST_CLASS_NAME(test_suite_name, test_name) test_suite_name ## _ ## test_name ## _AsyncTest

#define ASYNC_TEST_(test_suite_name, test_name, parent_class, parent_id) \
class ASYNC_TEST_CLASS_NAME(test_suite_name, test_name) \
    : public parent_class \
{ \
public: \
    ::Phantom::Coroutines::reusable_task<> AsyncTestBody(); \
}; \
\
GTEST_TEST_(test_suite_name, test_name, ASYNC_TEST_CLASS_NAME(test_suite_name, test_name), ::testing::internal::GetTestTypeId()) \
{ \
    ::Phantom::Coroutines::Test::ExecuteTest(AsyncTestBody()); \
} \
\
::Phantom::Coroutines::reusable_task<> ASYNC_TEST_CLASS_NAME(test_suite_name, test_name)::AsyncTestBody()

#define ASYNC_TEST(test_suite_name, test_name) ASYNC_TEST_(test_suite_name, test_name, ::testing::Test, ::testing::internal::GetTestTypeId())
#define ASYNC_TEST_F(test_suite_name, test_name) ASYNC_TEST_(test_suite_name, test_name, test_suite_name, ::testing::internal::GetTypeId<test_suite_name>())

#endif
