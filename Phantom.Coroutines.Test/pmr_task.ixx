module;
#include <memory>
#include <memory_resource>
#include "Phantom.Coroutines/detail/config.h"
#include "Phantom.Coroutines/task.h"
export module Phantom.Coroutines.Test.pmr_task;
import Phantom.Coroutines.promise_allocator;
import Phantom.Coroutines.reusable_task;
#include "pmr_task.h"
