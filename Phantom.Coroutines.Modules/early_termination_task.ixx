module;
#include <assert.h>
#include <concepts>
#include <exception>
#include <optional>
#include <tuple>
#include <type_traits>
#include <variant>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.early_termination_task;
import Phantom.Coroutines.await_all_await_transform;
import Phantom.Coroutines.awaiter_wrapper;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.final_suspend_transfer;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.variant_result_storage;
#include "Phantom.Coroutines/early_termination_task.h"
