module;
#include <assert.h>
#include <mutex>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.async_reader_writer_lock;
import Phantom.Coroutines.awaiter_list;
import Phantom.Coroutines.double_wide_atomic;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.policies;
import Phantom.Coroutines.tagged_pointer;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/async_reader_writer_lock.h"
