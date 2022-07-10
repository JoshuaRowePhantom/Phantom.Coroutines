export module Phantom.Coroutines.immovable_object;

namespace Phantom::Coroutines
{
export class immovable_object
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
