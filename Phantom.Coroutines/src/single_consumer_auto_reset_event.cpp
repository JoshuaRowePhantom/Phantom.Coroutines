#include "Phantom.Coroutines/single_consumer_auto_reset_event.h"

namespace Phantom::Coroutines::detail
{

//void single_consumer_auto_reset_event::set()
//{
//    State<> expectedState = m_state.load(
//        std::memory_order_acquire);
//
//    while (true)
//    {
//        if (expectedState == State<SignalledState>())
//        {
//            return;
//        }
//
//        if (expectedState == State<NotSignalledState>()
//            &&
//            !m_state.compare_exchange_weak(
//                expectedState,
//                State<SignalledState>(),
//                std::memory_order_release))
//        {
//            continue;
//        }
//
//
//    }
//}

}