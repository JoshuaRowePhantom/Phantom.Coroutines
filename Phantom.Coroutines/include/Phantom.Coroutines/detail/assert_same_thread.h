#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once

#if !NDEBUG
#include <assert.h>
#include <thread>
#endif
#endif

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