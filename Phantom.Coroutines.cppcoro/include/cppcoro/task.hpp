#include "Phantom.Coroutines/task.h"

namespace cppcoro
{

template<
    typename T = void
>
using task = Phantom::Coroutines::task<T>;

}
