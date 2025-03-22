#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_ASYNC_MUTEX_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_ASYNC_MUTEX_HPP

#include "Phantom.Coroutines/async_mutex.h"

namespace cppcoro
{
using async_mutex = ::Phantom::Coroutines::async_mutex<>;
using async_mutex_lock = typename async_mutex::lock_type;
using async_mutex_lock_operation = typename async_mutex::lock_operation;
using async_mutex_scoped_lock_operation = typename async_mutex::scoped_lock_operation;
}
#endif
