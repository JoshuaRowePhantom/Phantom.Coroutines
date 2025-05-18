module;
#include <atomic>
#include <cstddef>
#include <memory>
#include <memory_resource>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.Test.pmr_task;
import Phantom.Coroutines.promise_allocator;
import Phantom.Coroutines.reusable_task;
import Phantom.Coroutines.task;
#include "pmr_task.h"
