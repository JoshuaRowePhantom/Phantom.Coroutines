module;
#include <assert.h>
#include <atomic>
#include <concepts>
#include <memory>
#include <mutex>
#include <thread>
#include <unordered_set>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.read_copy_update;
import Phantom.Coroutines.assert_same_thread;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.nonatomic_shared_ptr;
import Phantom.Coroutines.scope_guard;
import Phantom.Coroutines.thread_local_storage;
#include "Phantom.Coroutines/read_copy_update.h"
