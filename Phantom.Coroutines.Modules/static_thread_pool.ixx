module;
#include <latch>
#include <thread>
#include <vector>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.static_thread_pool;
import Phantom.Coroutines.scheduler;
import Phantom.Coroutines.thread_pool_scheduler;
#include "Phantom.Coroutines/static_thread_pool.h"

