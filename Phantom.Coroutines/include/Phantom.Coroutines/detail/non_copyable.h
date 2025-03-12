#pragma once

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
