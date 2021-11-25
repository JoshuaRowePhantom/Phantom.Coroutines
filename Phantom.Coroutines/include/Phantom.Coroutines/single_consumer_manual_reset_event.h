#pragma once

#include "detail/single_consumer_event.h"

namespace Phantom::Coroutines
{
namespace detail
{
class single_consumer_manual_reset_event
    :
public single_consumer_event<
    single_consumer_event_states::SignalledState
>
{
    using single_consumer_manual_reset_event::single_consumer_event::single_consumer_event;
};

}
using detail::single_consumer_manual_reset_event;
}
