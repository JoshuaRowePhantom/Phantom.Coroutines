#include <gtest/gtest.h>
#include "Phantom.Coroutines/read_copy_update.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(read_copy_update_test, can_read_initial_value)
{
	read_copy_update_section<std::string> section("hello world");
	ASSERT_TRUE(*section.read() == "hello world");
	ASSERT_TRUE(*section.read() == "hello world");
	ASSERT_TRUE(*section.operator->() == "hello world");
	// Verify we can call object methods via operator->
	ASSERT_EQ(section->begin(), section.read()->begin());
}

TEST(read_copy_update_test, can_read_written_const_value)
{
	read_copy_update_section<const std::string> section("hello world 1");
	section.emplace("hello world 2");
	ASSERT_EQ(*section.read(), "hello world 2");
}

TEST(read_copy_update_test, can_modify_value_before_exchange)
{
	read_copy_update_section<const std::string> section("hello world 1");
	
	auto operation = section.update();
	operation.emplace("hello world 2")[0] = '2';
	operation.exchange();

	ASSERT_EQ(*section.read(), "2ello world 2");
}

TEST(read_copy_update_test, can_read_modified_and_replacement_value_after_failed_exchange_and_then_succeed)
{
	read_copy_update_section<const std::string> section("hello world 1");

	auto operation1 = section.update();
	auto operation2 = section.update();

	operation1.emplace("hello world 2");
	
	ASSERT_EQ(operation1.value(), "hello world 1");

	operation2.emplace("hello world 3");
	operation2.exchange();

	ASSERT_EQ(false, operation1.compare_exchange_strong());
	// As a result of the compare_exchange_strong, operation1's current value()
	// is updated to the result of operation2.exchange()
	ASSERT_EQ(operation1.value(), "hello world 3");
	ASSERT_EQ(operation1.replacement(), "hello world 2");

	ASSERT_EQ(operation2.value(), "hello world 3");

	ASSERT_EQ(true, operation1.compare_exchange_strong());
}

TEST(read_copy_update_test, can_read_new_value_after_exchange)
{
	read_copy_update_section<const std::string> section("hello world 1");

	auto operation = section.update();
	operation.emplace("hello world 2");
	operation.exchange();

	ASSERT_EQ(operation.value(), "hello world 2");
}

TEST(read_copy_update_test, can_read_written_value)
{
	read_copy_update_section<std::string> section("hello world 1");
	section.emplace("hello world 2");
	ASSERT_EQ(*section.read(), "hello world 2");
}

TEST(read_copy_update_test, read_continues_to_return_value_at_beginning_of_read_when_replaced)
{
	read_copy_update_section<std::string> section("hello world 1");
	auto readOperation1 = section.read();
	section.emplace("hello world 2");
	ASSERT_EQ(*readOperation1, "hello world 1");
}

typedef read_copy_update_section<std::string> rcu_string;
typedef read_copy_update_section<const std::string> rcu_const_string;

extern rcu_string declval_rcu_string;
extern rcu_const_string declval_rcu_const_string;

static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.read())>);
static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.operator->())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.read())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.operator->())>);
