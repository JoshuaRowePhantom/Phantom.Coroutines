#include "async_test.h"
#include "../Phantom.Coroutines.Test/lifetime_tracker.h"
#include "cppcoro/async_generator.hpp"

namespace cppcoro
{
ASYNC_TEST(cppcoro_async_generator_test, can_enumerate_items)
{
    auto lambda = []() -> async_generator<std::string>
    {
        co_yield "hello";
        co_yield "world";
    };

    auto generator = lambda();
    std::vector<std::string> items;
    for (auto iterator = co_await generator.begin();
        iterator != generator.end();
        co_await ++iterator)
    {
        items.push_back(*iterator);
    }

    EXPECT_EQ(items, (std::vector<std::string>{ "hello", "world" }));
}

ASYNC_TEST(cppcoro_async_generator_test, destroys_promise)
{
    Phantom::Coroutines::lifetime_statistics statistics;

    auto lambda = [&]() -> async_generator<std::string>
    {
        auto tracker = statistics.tracker();
        co_yield "hello";
        co_yield "world";
    };

    {
        auto generator = lambda();
        EXPECT_EQ(0, statistics.instance_count);
        auto iterator = co_await generator.begin();
        EXPECT_EQ(1, statistics.instance_count);
        EXPECT_EQ("hello", *iterator);
    }

    EXPECT_EQ(0, statistics.instance_count);
}

}