module;
#include <coroutine>
#include <concepts>
#include <exception>
#include <type_traits>
#include <utility>
#include <variant>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.core_task;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.non_copyable;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.variant_result_storage;
#include "Phantom.Coroutines/detail/core_task.h"
