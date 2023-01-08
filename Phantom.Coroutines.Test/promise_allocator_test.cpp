#include "async_test.h"
#include "Phantom.Coroutines/promise_allocator.h"
#include <memory_resource>

namespace Phantom::Coroutines
{

namespace
{

struct memory_tracker_data
{
    size_t m_allocatedMemory = 0;
};

class memory_tracker : 
    public std::pmr::memory_resource
{
    std::shared_ptr<memory_tracker_data> m_trackerData 
        = std::make_shared<memory_tracker_data>();

    // Inherited via memory_resource
    virtual void* do_allocate(size_t _Bytes, size_t _Align) override
    {
        m_trackerData->m_allocatedMemory += _Bytes;
        return new char[_Bytes];
    }

    virtual void do_deallocate(void* _Ptr, size_t _Bytes, size_t _Align) override
    {
        m_trackerData->m_allocatedMemory -= _Bytes;
        delete _Ptr;
    }

    virtual bool do_is_equal(const memory_resource& _That) const noexcept override
    {
        return false;
    }

public:
    size_t allocated_memory() const
    {
        return m_trackerData->m_allocatedMemory;
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

}
