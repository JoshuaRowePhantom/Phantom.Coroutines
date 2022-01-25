#include <optional>
#include <gtest/gtest.h>
#include "Phantom.Coroutines/reusable_consecutive_global_id.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

TEST(reusable_consecutive_global_id_test, starts_at_zero_and_increments)
{
	struct label;
	reusable_consecutive_global_id<label> id0;
	reusable_consecutive_global_id<label> id1;
	reusable_consecutive_global_id<label> id2;
	ASSERT_EQ(0, id0);
	ASSERT_EQ(0, id0.get());
	ASSERT_EQ(1, id1);
	ASSERT_EQ(1, id1.get());
	ASSERT_EQ(2, id2);
	ASSERT_EQ(2, id2.get());
}

TEST(reusable_consecutive_global_id_test, reuses_most_recent_freed_id)
{
	struct label;
	reusable_consecutive_global_id<label> id0;
	std::optional<reusable_consecutive_global_id<label>> id1{ reusable_consecutive_global_id<label>{} };
	std::optional<reusable_consecutive_global_id<label>> id2{ reusable_consecutive_global_id<label>{} };
	ASSERT_EQ(0, id0);
	ASSERT_EQ(0, id0.get());
	ASSERT_EQ(1, *id1);
	ASSERT_EQ(1, id1->get());
	ASSERT_EQ(2, *id2);
	ASSERT_EQ(2, id2->get());
	id2.reset();
	id1.reset();
	reusable_consecutive_global_id<label> id3;
	reusable_consecutive_global_id<label> id4;
	reusable_consecutive_global_id<label> id5;
	ASSERT_EQ(1, id3);
	ASSERT_EQ(1, id3);
	ASSERT_EQ(2, id4);
	ASSERT_EQ(2, id4);
	ASSERT_EQ(3, id5);
	ASSERT_EQ(3, id5);
}

TEST(reusable_consecutive_global_id_test, moved_constructor_from_id_doesnt_get_reused)
{
	struct label;
	std::optional<reusable_consecutive_global_id<label>> id0{ {} };
	reusable_consecutive_global_id<label> id1{ std::move(*id0) };
	id0.reset();
	reusable_consecutive_global_id<label> id2;

	ASSERT_EQ(0, id1);
	ASSERT_EQ(1, id2);
}

TEST(reusable_consecutive_global_id_test, moved_into_id_does_get_reused)
{
	struct label;
	std::optional<reusable_consecutive_global_id<label>> id0{ {} };
	reusable_consecutive_global_id<label> id1;
	id1 = std::move(*id0);
	id0.reset();
	reusable_consecutive_global_id<label> id2;

	ASSERT_EQ(0, id1);
	ASSERT_EQ(1, id2);
}

struct reusable_consecutive_global_id_test_global_label;
static_assert(!std::copyable<reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>>);
static_assert(!std::copy_constructible<reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>>);
static_assert(!std::assignable_from<reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>&, reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>&>);
static_assert(!std::assignable_from<reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>&, const reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>&>);
static_assert(!std::assignable_from<reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>&, const reusable_consecutive_global_id<reusable_consecutive_global_id_test_global_label>>);
