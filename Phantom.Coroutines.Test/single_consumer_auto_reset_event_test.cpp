#include <gtest/gtest.h>
#include "Phantom.Coroutines/single_consumer_auto_reset_event.h"

namespace Phantom::Coroutines
{

TEST(single_consumer_auto_reset_event_test, Can_default_initialize)
{
    single_consumer_auto_reset_event event;
}

TEST(single_consumer_auto_reset_event_test, Starts_as_not_set)
{
    single_consumer_auto_reset_event event;
    ASSERT_FALSE(event.is_set());
}

TEST(single_consumer_auto_reset_event_test, Starts_as_not_set_explicitly)
{
    single_consumer_auto_reset_event event(false);
    ASSERT_FALSE(event.is_set());
}

TEST(single_consumer_auto_reset_event_test, Starts_as_set_explicitly)
{
    single_consumer_auto_reset_event event(true);
    ASSERT_TRUE(event.is_set());
}

TEST(single_consumer_auto_reset_event_test, Can_be_reset_after_set)
{
    single_consumer_auto_reset_event event(true);
    event.reset();
    ASSERT_FALSE(event.is_set());
}

}