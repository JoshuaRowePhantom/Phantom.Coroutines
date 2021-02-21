#pragma once
#include <coroutine>

namespace Phantom::Coroutines
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

}