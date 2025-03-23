module;
#include <assert.h>
#include <exception>
#include <future>
#include "Phantom.coroutines/detail/config.h"
#ifdef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#include <optional>
#include "Phantom.Coroutines/task.h"
#endif
export module Phantom.Coroutines.sync_wait;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.type_traits;
#include "Phantom.coroutines/sync_wait.h"
