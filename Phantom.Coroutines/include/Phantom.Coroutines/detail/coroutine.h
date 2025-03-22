#ifndef PHANTOM_COROUTINES_INCLUDE_COROUTINE_H
#define PHANTOM_COROUTINES_INCLUDE_COROUTINE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "Phantom.Coroutines/detail/config.h"
#include <assert.h>
#include <coroutine>
#include <tuple>
#endif

#include "assert_is_configured_module.h"

namespace Phantom::Coroutines
{
namespace detail
{
using std::coroutine_traits;

template<
    typename TPromise = void
>
using coroutine_handle = std::coroutine_handle<TPromise>;

using suspend_always = std::suspend_always;

using suspend_never = std::suspend_never;

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

PHANTOM_COROUTINES_MODULE_EXPORT
constexpr auto operator<=>(const coroutine_handle<>& left, const coroutine_handle<> right)
{
    return std::operator<=>(left, right);
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<typename Promise>
constexpr auto operator==(const coroutine_handle<>& left, const coroutine_handle<> right)
{
    return std::operator==(left, right);
}

}

namespace std
{
PHANTOM_COROUTINES_MODULE_EXPORT
using std::coroutine_traits;

PHANTOM_COROUTINES_MODULE_EXPORT
using std::operator==;
PHANTOM_COROUTINES_MODULE_EXPORT
using std::operator<=>;
}
#endif
