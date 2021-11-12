#pragma once

namespace Phantom::Coroutines::detail
{
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
