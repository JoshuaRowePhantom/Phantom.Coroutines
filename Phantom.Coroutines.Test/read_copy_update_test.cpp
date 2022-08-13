import "gtest.h";
import Phantom.Coroutines.read_copy_update;
import Phantom.Coroutines.Test.lifetime_tracker;
import<optional>;

namespace Phantom::Coroutines
{

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

TEST(read_copy_update_test, can_refresh_to_read_new_value)
{
	read_copy_update_section<const std::string> section("hello world 1");

	auto operation = section.update();
	section.emplace("hello world 2");
	ASSERT_EQ(operation.value(), "hello world 1");
	operation.refresh();
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

TEST(read_copy_update_test, object_released_after_replace_and_reread)
{
	lifetime_statistics statistics1;
	read_copy_update_section<lifetime_tracker> section{ statistics1.tracker() };

	ASSERT_EQ(1, statistics1.instance_count);

	lifetime_statistics statistics2;
	section.write().emplace(statistics2.tracker());

	ASSERT_EQ(1, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);

	std::ignore = section.operator->();

	ASSERT_EQ(0, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);
}

TEST(read_copy_update_test, object_released_after_replace_and_last_reader_released_and_reread)
{
	lifetime_statistics statistics1;
	read_copy_update_section<lifetime_tracker> section{ statistics1.tracker() };
	std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation1(section);
	std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation2(section);
	std::optional<read_copy_update_section<lifetime_tracker>::read_operation> readOperation3(section);

	(*readOperation1)->use();
	(*readOperation2)->use();
	(*readOperation3)->use();

	ASSERT_EQ(1, statistics1.instance_count);

	lifetime_statistics statistics2;
	section.write().emplace(statistics2.tracker());

	(*readOperation1)->use();
	(*readOperation2)->use();
	(*readOperation3)->use();

	ASSERT_EQ(1, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);

	readOperation2.reset();
	(*readOperation1)->use();
	(*readOperation3)->use();

	ASSERT_EQ(1, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);

	readOperation3.reset();
	(*readOperation1)->use();

	ASSERT_EQ(1, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);

	readOperation1.reset();

	ASSERT_EQ(1, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);

	std::ignore = section.operator->();
	ASSERT_EQ(0, statistics1.instance_count);
	ASSERT_EQ(1, statistics2.instance_count);
}

typedef read_copy_update_section<std::string> rcu_string;
typedef read_copy_update_section<const std::string> rcu_const_string;

extern rcu_string declval_rcu_string;
extern rcu_const_string declval_rcu_const_string;

static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.read())>);
static_assert(std::same_as<std::string&, decltype(*declval_rcu_string.operator->())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.read())>);
static_assert(std::same_as<const std::string&, decltype(*declval_rcu_const_string.operator->())>);
}
