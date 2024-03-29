#include "async_test.h"
#include "pmr_task.h"

namespace Phantom::Coroutines
{

namespace
{
using Test::memory_tracker_data;
using Test::memory_tracker;
using Test::pmr_task;

class throwing_memory_resource :
    public std::pmr::memory_resource
{
    // Inherited via memory_resource
    virtual void* do_allocate(size_t, size_t) override
    {
        throw std::bad_alloc();
    }

    virtual void do_deallocate(void*, size_t, size_t) override
    {
        EXPECT_TRUE(false);
    }

    virtual bool do_is_equal(const memory_resource&) const noexcept override
    {
        return false;
    }
};

class null_returning_memory_resource :
    public std::pmr::memory_resource
{
    // Inherited via memory_resource
    virtual void* do_allocate(size_t, size_t) override
    {
        return nullptr;
    }

    virtual void do_deallocate(void*, size_t, size_t) override
    {
        EXPECT_TRUE(false);
    }

    virtual bool do_is_equal(const memory_resource&) const noexcept override
    {
        return false;
    }
};

template<
    typename Result = void
> using allocated_task = basic_task<
    promise_allocator<
        task_promise<Result>,
        std::pmr::polymorphic_allocator<>
    >
>;

struct convertible_to_task
{
    template<typename Task> operator Task()
    {
        return Task();
    }
};

struct get_return_object_on_allocation_failure_promise
    :
    public derived_promise<task_promise<void>>
{
    static convertible_to_task get_return_object_on_allocation_failure()
    {
        return {};
    }
};

using allocated_nothrow_task = basic_task<
    promise_allocator<
        get_return_object_on_allocation_failure_promise,
        std::pmr::polymorphic_allocator<>
    >
>;

}

ASYNC_TEST(promise_allocator_test, can_co_await_allocated_promise)
{
    memory_tracker tracker;
    auto allocator = std::pmr::polymorphic_allocator(&tracker);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_task<>
    {
        co_return;
    };

    co_await lambda(allocator);
}

ASYNC_TEST(promise_allocator_test, allocated_promise_uses_passed_in_allocator_as_first_argument_of_lambda)
{
    memory_tracker tracker;
    auto allocator = std::pmr::polymorphic_allocator(&tracker);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_task<>
    {
        EXPECT_NE(0, tracker.allocated_memory());
        co_return;
    };

    co_await lambda(allocator);
    EXPECT_EQ(0, tracker.allocated_memory());
}

ASYNC_TEST(promise_allocator_test, allocated_promise_uses_passed_in_allocator_as_second_argument_of_lambda)
{
    memory_tracker tracker;
    auto allocator = std::pmr::polymorphic_allocator(&tracker);

    auto lambda = [&](int x, std::pmr::polymorphic_allocator<>) -> allocated_task<>
    {
        EXPECT_EQ(5, x);
        EXPECT_NE(0, tracker.allocated_memory());
        co_return;
    };

    co_await lambda(5, allocator);
    EXPECT_EQ(0, tracker.allocated_memory());
}

ASYNC_TEST(promise_allocator_test, allocated_promise_does_not_use_nothrow_if_no_static_get_return_object_on_allocation_failure)
{
    throwing_memory_resource failingAllocator;
    auto allocator = std::pmr::polymorphic_allocator(&failingAllocator);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_task<>
    {
        EXPECT_FALSE(true);
        co_return;
    };

    EXPECT_THROW(std::ignore = lambda(allocator), std::bad_alloc);
    co_return;
}

ASYNC_TEST(promise_allocator_test, allocated_promise_catches_bad_alloc_if_static_get_return_object_on_allocation_failure)
{
    throwing_memory_resource failingAllocator;
    auto allocator = std::pmr::polymorphic_allocator(&failingAllocator);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_nothrow_task
    {
        EXPECT_FALSE(true);
        co_return;
    };

    auto task = lambda(allocator);
    EXPECT_TRUE(!task);
    co_return;
}

ASYNC_TEST(promise_allocator_test, allocated_promise_returns_null_if_static_get_return_object_on_allocation_failure_and_allocation_failure)
{
    null_returning_memory_resource failingAllocator;
    auto allocator = std::pmr::polymorphic_allocator(&failingAllocator);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_nothrow_task
    {
        EXPECT_FALSE(true);
        co_return;
    };

    auto task = lambda(allocator);
    EXPECT_TRUE(!task);
    co_return;
}

ASYNC_TEST(promise_allocator_test, allocated_promise_returns_non_null_if_static_get_return_object_on_allocation_failure_and_allocation_success)
{
    auto allocator = std::pmr::polymorphic_allocator(std::pmr::get_default_resource());

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_nothrow_task
    {
        EXPECT_FALSE(true);
        co_return;
    };

    auto task = lambda(allocator);
    EXPECT_TRUE(task);
    co_return;
}

}
