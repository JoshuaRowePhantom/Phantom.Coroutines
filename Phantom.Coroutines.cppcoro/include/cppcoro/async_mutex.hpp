#pragma once

#include "Phantom.Coroutines/async_mutex.h"

namespace cppcoro
{
using async_mutex = ::Phantom::Coroutines::async_mutex<>;
using async_mutex_lock = typename async_mutex::lock_type;
}