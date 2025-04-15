module;
#include <assert.h>
#include <atomic>
#include <exception>
#include <optional>
#include <tuple>
#include <utility>
#include <variant>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.shared_task;
import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.variant_result_storage;
#include "Phantom.Coroutines/shared_task.h"

