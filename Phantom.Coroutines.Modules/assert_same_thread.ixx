module;
#if !NDEBUG
#include <assert.h>
#include <thread>
#endif
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.assert_same_thread;
#include "Phantom.Coroutines/detail/assert_same_thread.h"
