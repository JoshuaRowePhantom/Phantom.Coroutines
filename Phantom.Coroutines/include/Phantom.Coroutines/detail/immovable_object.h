#ifndef PHANTOM_COROUTINES_INCLUDE_IMMOVABLE_OBJECT_H
#define PHANTOM_COROUTINES_INCLUDE_IMMOVABLE_OBJECT_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "config.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

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
#endif
