#pragma once

namespace Phantom::Coroutines::detail
{
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
