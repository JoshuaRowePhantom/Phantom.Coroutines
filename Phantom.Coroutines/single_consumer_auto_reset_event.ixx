export module Phantom.Coroutines.single_consumer_auto_reset_event;

import Phantom.Coroutines.single_consumer_event;

namespace Phantom::Coroutines
{

export class single_consumer_auto_reset_event
    :
public single_consumer_event<
    single_consumer_event_states::NotSignalledState
>
{
    using single_consumer_auto_reset_event::single_consumer_event::single_consumer_event;
};

}
