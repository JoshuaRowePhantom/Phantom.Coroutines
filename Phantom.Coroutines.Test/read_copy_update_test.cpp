#include <gtest/gtest.h>
#include "Phantom.Coroutines/read_copy_update.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(read_copy_update_test, can_read_initial_value)
{
	read_copy_update_section<std::string> section("hello world");
	ASSERT_TRUE(*section.read() == "hello world");
	ASSERT_TRUE(*section.read().operator->() == "hello world");
}
