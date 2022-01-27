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

TEST(read_copy_update_test, can_read_written_value)
{
	read_copy_update_section<std::string> section("hello world 1");
	section.emplace("hello world 2");
	ASSERT_EQ(*section.read(), "hello world 2");
}

TEST(read_copy_update_test, read_continues_to_return_value_at_beginning_of_read_when_replaced_on_same_thread)
{
	read_copy_update_section<std::string> section("hello world 1");
	auto readOperation1 = section.read();
	section.emplace("hello world 2");
	ASSERT_EQ(*readOperation1, "hello world 1");
}
