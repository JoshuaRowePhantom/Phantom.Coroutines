#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once
#include "../reusable_consecutive_global_id.h"
#endif

namespace Phantom::Coroutines::detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
class consecutive_thread_id
{
    static inline thread_local size_t consecutive_thread_id_current_value = 0;
    using id_generator_type = reusable_consecutive_global_id<
        struct thread_id_label,
        size_t,
        1
    >;

    [[msvc::noinline]]
    static size_t construct_current()
    {
        static thread_local id_generator_type generator;

        return consecutive_thread_id_current_value = generator;
    }

public:
    static size_t current()
    {
        if (consecutive_thread_id_current_value)
        {
            return consecutive_thread_id_current_value;
        }

        return construct_current();
    }
};
}
