module;
#if __cpp_lib_atomic_shared_ptr
#include <memory>
#else
#include <atomic>
#include <concepts>
#include <mutex>
#endif
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.atomic_shared_ptr;
#include "Phantom.Coroutines/detail/atomic_shared_ptr.h"
