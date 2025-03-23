module;
#include <assert.h>
#include <algorithm>
#include <atomic>
#include <bit>
#include <shared_mutex>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.thread_pool_scheduler;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.read_copy_update;
import Phantom.Coroutines.scheduler;
import Phantom.Coroutines.task;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/thread_pool_scheduler.h"
