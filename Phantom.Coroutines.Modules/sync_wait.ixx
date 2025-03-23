module;
#include <assert.h>
#include <exception>
#include <future>
#include "Phantom.Coroutines/detail/config.h"
#ifdef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#include <optional>
#endif
export module Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/sync_wait.h"
