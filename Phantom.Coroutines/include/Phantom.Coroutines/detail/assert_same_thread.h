#ifndef PHANTOM_COROUTINES_INCLUDE_ASSERT_SAME_THREAD_H
#define PHANTOM_COROUTINES_INCLUDE_ASSERT_SAME_THREAD_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#if !NDEBUG
#include <assert.h>
#include <thread>
#endif
#endif

#include "assert_is_configured_module.h"

namespace Phantom::Coroutines::detail
{

#if NDEBUG
PHANTOM_COROUTINES_MODULE_EXPORT
class assert_same_thread
{
public:
    assert_same_thread()
    {
    }

    void check_thread() const
    {
    }

    ~assert_same_thread()
    {
    }
};
#else
PHANTOM_COROUTINES_MODULE_EXPORT
class assert_same_thread
{
    std::thread::id m_threadId;
public:
    assert_same_thread()
        :
        m_threadId{ std::this_thread::get_id() }
    {
    }

    void check_thread() const
    {
        assert(m_threadId == std::this_thread::get_id());
    }

    ~assert_same_thread()
    {
        check_thread();
    }
};
#endif

}
#endif
