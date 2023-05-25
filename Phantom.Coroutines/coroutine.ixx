export module Phantom.Coroutines.coroutine;

import <assert.h>;
import <coroutine>;

namespace Phantom::Coroutines
{
export template<
    typename TPromise = void
>
using coroutine_handle = std::coroutine_handle<TPromise>;
export using suspend_always = std::suspend_always;
export using suspend_never = std::suspend_never;

export auto noop_coroutine()
{
    return std::noop_coroutine();
}

// Create a coroutine handle that is not null but isn't valid either,
// for debugging purposes.
export auto invalid_coroutine_handle()
{
    return coroutine_handle<>::from_address(
        reinterpret_cast<void*>(0x0cfcfcfcfcfcfcfcULL)
    );
}

export template<
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

export bool is_valid(
    coroutine_handle<> coroutine
)
{
    return coroutine && coroutine != invalid_coroutine_handle();
}

export void assert_is_valid(
    coroutine_handle<> coroutine
)
{
    assert(is_valid(coroutine));
}

}