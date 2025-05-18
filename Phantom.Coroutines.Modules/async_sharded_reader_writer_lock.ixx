module;
#include <mutex>
#include <type_traits>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.async_sharded_reader_writer_lock;
import Phantom.Coroutines.async_reader_writer_lock;
import Phantom.Coroutines.direct_initialized_optional;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.scope_guard;
import Phantom.Coroutines.sharding;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/async_sharded_reader_writer_lock.h"
