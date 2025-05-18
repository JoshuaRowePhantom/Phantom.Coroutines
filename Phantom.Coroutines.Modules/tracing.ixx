module;
#include <concepts>
#include <exception>
#include <source_location>
#include <tuple>
#include <type_traits>
#include <utility>
#include "Phantom.Coroutines/detail/config_macros.h"
export module Phantom.Coroutines.tracing;
import Phantom.Coroutines.awaiter_wrapper;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/tracing.h"
