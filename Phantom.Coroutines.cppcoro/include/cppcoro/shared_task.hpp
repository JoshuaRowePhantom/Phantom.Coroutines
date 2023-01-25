#include "Phantom.Coroutines/shared_task.h"

namespace cppcoro
{

template<
    typename T = void
>
using shared_task = Phantom::Coroutines::shared_task<T>;

}
