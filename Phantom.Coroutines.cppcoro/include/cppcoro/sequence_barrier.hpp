#pragma once

#include "Phantom.Coroutines/async_sequence_barrier.h"
#include "task.hpp"

namespace cppcoro
{

template<
    typename Value
> class sequence_barrier
    :
    public ::Phantom::Coroutines::async_sequence_barrier<Value> 
{
    using ::Phantom::Coroutines::async_sequence_barrier<Value>::async_sequence_barrier;

public:
    task<Value> wait_until_published(
        Value value,
        auto& scheduler
    )
    {
        auto result = co_await this->::Phantom::Coroutines::async_sequence_barrier<Value>::wait_until_published(
            value);
        co_await scheduler.schedule();
        co_return result;
    }
};

}