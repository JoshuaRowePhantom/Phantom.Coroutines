module;
#include <atomic>
#include <concepts>
#include <mutex>
#include <type_traits>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.async_mutex;
import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.awaiter_list;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.non_copyable;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/async_mutex.h"
