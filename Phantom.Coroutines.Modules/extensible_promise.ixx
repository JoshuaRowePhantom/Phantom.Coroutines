module;
#include <concepts>
#include <exception>
#include <optional>
#include <tuple>
#include <type_traits>
#include "Phantom.Coroutines/detail/config.h"
export module Phantom.Coroutines.extensible_promise;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.scope_guard;
import Phantom.Coroutines.type_traits;
#include "Phantom.Coroutines/extensible_promise.h"
#include "Phantom.Coroutines/awaiter_wrapper.h"
