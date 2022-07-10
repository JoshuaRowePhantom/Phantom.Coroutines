export module Phantom.Coroutines.non_copyable;

namespace Phantom::Coroutines
{
    export class noncopyable
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
