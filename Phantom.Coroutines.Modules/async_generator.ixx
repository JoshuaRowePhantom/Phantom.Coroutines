module;
#include <concepts>
#include <exception>
#include <variant>
#include <type_traits>
#include "Phantom.Coroutines/detail/config.h"
#include "Phantom.Coroutines/task.h"
export module Phantom.Coroutines.async_generator;
export import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.awaiter_wrapper;
import Phantom.Coroutines.extensible_promise;
#include "Phantom.Coroutines/async_generator.h"
