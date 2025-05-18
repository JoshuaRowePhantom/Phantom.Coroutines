module;
#include <assert.h>
#include <future>
#include <mutex>
#include <concepts>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.awaiter_list;
import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.policies;
#include "Phantom.Coroutines/awaiter_list.h"
