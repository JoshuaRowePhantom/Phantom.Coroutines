#ifndef PHANTOM_COROUTINES_INCLUDE_NON_COPYABLE_H
#define PHANTOM_COROUTINES_INCLUDE_NON_COPYABLE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "Phantom.Coroutines/detail/config.h"
#endif

#include "assert_is_configured_module.h"

namespace Phantom::Coroutines::detail
{
PHANTOM_COROUTINES_MODULE_EXPORT
class noncopyable
{
protected:
    noncopyable() {}

private:
    noncopyable(
        const noncopyable&
    );

    noncopyable& operator=(
        const noncopyable&
        ) = delete;
};
}
#endif
