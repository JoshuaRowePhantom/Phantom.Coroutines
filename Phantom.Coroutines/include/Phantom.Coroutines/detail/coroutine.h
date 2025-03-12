#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once
#include "Phantom.Coroutines/detail/config.h"
#include <assert.h>
#include <coroutine>
#include <tuple>
#endif

namespace Phantom::Coroutines
{
namespace detail
{
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TPromise = void
>
using coroutine_handle = std::coroutine_handle<TPromise>;

PHANTOM_COROUTINES_MODULE_EXPORT
using suspend_always = std::suspend_always;

PHANTOM_COROUTINES_MODULE_EXPORT
using suspend_never = std::suspend_never;

PHANTOM_COROUTINES_MODULE_EXPORT
inline auto noop_coroutine()
{
    return std::noop_coroutine();
}

// Create a coroutine handle that is not null but isn't valid either,
// for debugging purposes.
PHANTOM_COROUTINES_MODULE_EXPORT
inline auto invalid_coroutine_handle()
{
    return coroutine_handle<>::from_address(
        reinterpret_cast<void*>(0x0cfcfcfcfcfcfcfcULL)
    );
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
>
auto copy_and_invalidate(
    coroutine_handle<Promise>& handle
)
{
    auto result = handle;
#ifndef NDEBUG
    handle = invalid_coroutine_handle();
#endif
    return result;
}

PHANTOM_COROUTINES_MODULE_EXPORT
inline bool is_valid(
    coroutine_handle<> coroutine
)
{
    return coroutine && coroutine != invalid_coroutine_handle();
}

PHANTOM_COROUTINES_MODULE_EXPORT
inline void assert_is_valid(
    coroutine_handle<> coroutine
)
{
    std::ignore = coroutine;
    assert(is_valid(coroutine));
}
}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::coroutine_handle;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::suspend_always;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::suspend_never;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::noop_coroutine;

}