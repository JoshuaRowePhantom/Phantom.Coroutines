#pragma once

#include "Phantom.Coroutines/awaiter_wrapper.h"
#include "Phantom.Coroutines/task.h"

namespace cppcoro
{

template<
    typename Value = void
>
class [[nodiscard]] task
    :
    public ::Phantom::Coroutines::awaiter_wrapper<::Phantom::Coroutines::task<Value>>
{
public:
    using promise_type = typename ::Phantom::Coroutines::task<Value>::promise_type;

    task(
        ::Phantom::Coroutines::task<Value> underlyingTask
    ) : task::awaiter_wrapper([&]() -> decltype(auto) { return std::move(underlyingTask); })
    {}
};

}
