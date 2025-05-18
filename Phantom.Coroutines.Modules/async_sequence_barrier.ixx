module;
#include <assert.h>
#include <atomic>
#include <concepts>
#include <functional>
#include <limits>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.async_sequence_barrier;
import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.fibonacci_heap;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.policies;
#include "Phantom.Coroutines/async_sequence_barrier.h"
