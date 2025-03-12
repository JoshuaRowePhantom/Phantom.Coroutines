#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once
#include "Phantom.Coroutines/detail/config.h"
#endif

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
