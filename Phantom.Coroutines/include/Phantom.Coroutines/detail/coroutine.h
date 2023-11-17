#pragma once
#include <assert.h>
#include <coroutine>

namespace Phantom::Coroutines
{
namespace detail
{
template<
    typename TPromise = void
>
using coroutine_handle = std::coroutine_handle<TPromise>;
using suspend_always = std::suspend_always;
using suspend_never = std::suspend_never;

static inline auto noop_coroutine()
{
    return std::noop_coroutine();
}

// Create a coroutine handle that is not null but isn't valid either,
// for debugging purposes.
static auto invalid_coroutine_handle()
{
    return coroutine_handle<>::from_address(
        reinterpret_cast<void*>(0x0cfcfcfcfcfcfcfcULL)
    );
}

template<
    typename Promise
>
static auto copy_and_invalidate(
    coroutine_handle<Promise>& handle
)
{
    auto result = handle;
#ifndef NDEBUG
    handle = invalid_coroutine_handle();
#endif
    return result;
}

static bool is_valid(
    coroutine_handle<> coroutine
)
{
    return coroutine && coroutine != invalid_coroutine_handle();
}

__pragma(warning(suppress:4505))
static void assert_is_valid(
    coroutine_handle<> coroutine
)
{
    assert(is_valid(coroutine));
}
}

using detail::coroutine_handle;
using detail::suspend_always;
using detail::suspend_never;
using detail::noop_coroutine;

}