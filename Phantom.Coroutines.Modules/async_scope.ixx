module;
#include <assert.h>
#include <atomic>
#include <concepts>
#include <exception>
#include <functional>
#include <tuple>
#include <utility>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.async_scope;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/async_scope.h"
