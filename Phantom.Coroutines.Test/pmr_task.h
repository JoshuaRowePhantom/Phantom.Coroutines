#ifndef PHANTOM_COROUTINES_INCLUDE_PMR_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_PMR_TASK_H
#if defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include <atomic>
#include <cstddef>
#include <memory>
#include <memory_resource>
#include "Phantom.Coroutines/detail/config.h"
#include "Phantom.Coroutines/promise_allocator.h"
#include "Phantom.Coroutines/reusable_task.h"
#include "Phantom.Coroutines/task.h"
#endif

namespace Phantom::Coroutines::Test
{

PHANTOM_COROUTINES_MODULE_EXPORT
struct memory_tracker_data
{
    std::atomic<size_t> m_allocatedMemory = 0;
};

PHANTOM_COROUTINES_MODULE_EXPORT
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

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result = void
> using pmr_task = basic_task<
    promise_allocator<
        task_promise<Result>,
        std::pmr::polymorphic_allocator<>
    >
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result = void
> using pmr_reusable_task = basic_reusable_task<
    promise_allocator<
        reusable_task_promise<Result>,
        std::pmr::polymorphic_allocator<>
    >
>;

}
#endif
