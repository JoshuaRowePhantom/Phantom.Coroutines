#pragma once

#include <atomic>
#include "detail/atomic_state.h"
#include "detail/coroutine.h"

namespace Phantom::Coroutines
{
namespace detail
{
class single_consumer_auto_reset_event
{
    struct NotSignalledState;
    struct SignalledState;

    //StateHolder<
    //    coroutine_handle<>,
    //    NotSignalledState,
    //    SignalledState
    //> m_state;

public:
    single_consumer_auto_reset_event(
        bool initiallySignalled = false
    );

    void set();

    class awaiter
    {
        friend class single_consumer_auto_reset_event;

        awaiter(
            single_consumer_auto_reset_event& event
        );

    public:
        bool await_ready() noexcept;
        coroutine_handle<> await_suspend(coroutine_handle<>) noexcept;
        void await_resume() noexcept;
    };

    awaiter operator co_await();
};

}
using detail::single_consumer_auto_reset_event;
}
