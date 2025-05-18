module;
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <mutex>
#include <set>
#include <type_traits>
#include <vector>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.thread_local_storage;
import Phantom.Coroutines.atomic_shared_ptr;
import Phantom.Coroutines.consecutive_thread_id;
import Phantom.Coroutines.reusable_consecutive_global_id;
#include "Phantom.Coroutines/thread_local_storage.h"
