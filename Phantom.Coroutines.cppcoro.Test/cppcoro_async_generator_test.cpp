#include "../Phantom.Coroutines.Test/async_test.h"
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
}