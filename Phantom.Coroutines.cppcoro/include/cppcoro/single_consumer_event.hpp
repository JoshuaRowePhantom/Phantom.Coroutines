#pragma once

#include "Phantom.Coroutines/async_manual_reset_event.h"

namespace cppcoro
{
using single_consumer_event = ::Phantom::Coroutines::async_manual_reset_event<
    ::Phantom::Coroutines::single_awaiter
>;
}