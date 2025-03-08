#pragma once
#include "reusable_consecutive_global_id.h"

namespace Phantom::Coroutines::detail
{
static thread_local size_t consecutive_thread_id_current_value = 0;

class consecutive_thread_id
{
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
    [[msvc::noinline]]
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
