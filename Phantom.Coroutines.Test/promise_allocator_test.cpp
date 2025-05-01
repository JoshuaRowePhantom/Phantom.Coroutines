#include "async_test.h"
#include <memory_resource>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.pmr_task;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.promise_allocator;
import Phantom.Coroutines.task;
import Phantom.Coroutines.Test.pmr_task;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/promise_allocator.h"
#include "Phantom.Coroutines/task.h"
#include "pmr_task.h"
#endif

namespace Phantom::Coroutines
{

namespace
{
using Test::memory_tracker_data;
using Test::memory_tracker;
using Test::pmr_task;

class null_memory_resource :
    public std::pmr::memory_resource
{
    // Inherited via memory_resource
    virtual void* do_allocate(size_t, size_t) override
    {
        throw std::bad_alloc();
    }

    virtual void do_deallocate(void*, size_t, size_t) override
    {
    }

    virtual bool do_is_equal(const memory_resource& r) const noexcept override
    {
        return this == &r;
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

ASYNC_TEST(promise_allocator_test, allocated_promise_returns_null_if_static_get_return_object_on_allocation_failure_and_allocation_failure)
{
    null_memory_resource failingAllocator;
    auto allocator = std::pmr::polymorphic_allocator(&failingAllocator);

    auto lambda = [&](std::pmr::polymorphic_allocator<>) -> allocated_nothrow_task
    {
        EXPECT_FALSE(true);
        co_return;
    };

    // We use new here to work around HALO optimizing away the call to operator new.
    allocated_nothrow_task* task = new allocated_nothrow_task(lambda(allocator));
    EXPECT_NE(nullptr, task);
    EXPECT_TRUE(!*task);
    delete task;

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
