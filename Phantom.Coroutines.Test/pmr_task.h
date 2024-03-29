#pragma once

#include "Phantom.Coroutines/promise_allocator.h"
#include "Phantom.Coroutines/task.h"
#include "Phantom.Coroutines/reusable_task.h"
#include <memory_resource>

namespace Phantom::Coroutines::Test
{

struct memory_tracker_data
{
    std::atomic<size_t> m_allocatedMemory = 0;
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
        return std::pmr::get_default_resource()->allocate(_Bytes, _Align);
    }

    virtual void do_deallocate(void* _Ptr, size_t _Bytes, size_t _Align) override
    {
        m_trackerData->m_allocatedMemory -= _Bytes;
        return std::pmr::get_default_resource()->deallocate(_Ptr, _Bytes, _Align);
    }

    virtual bool do_is_equal(const memory_resource&) const noexcept override
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
> using pmr_task = basic_task<
    promise_allocator<
        task_promise<Result>,
        std::pmr::polymorphic_allocator<>
    >
>;

template<
    typename Result = void
> using pmr_reusable_task = basic_reusable_task<
    promise_allocator<
        reusable_task_promise<Result>,
        std::pmr::polymorphic_allocator<>
    >
>;


}