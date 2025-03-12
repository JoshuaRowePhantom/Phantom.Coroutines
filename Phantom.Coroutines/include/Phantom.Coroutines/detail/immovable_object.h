#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#pragma once
#include "config.h"
#endif

namespace Phantom::Coroutines::detail
{
PHANTOM_COROUTINES_MODULE_EXPORT
class immovable_object
{
protected:
    immovable_object(){}

private:
    immovable_object(
        const immovable_object&
        ) = delete;

    immovable_object(
        immovable_object&&
        ) = delete;

    immovable_object& operator=(
        const immovable_object&
        ) = delete;

    immovable_object& operator=(
        immovable_object&&
        ) = delete;
};
}
