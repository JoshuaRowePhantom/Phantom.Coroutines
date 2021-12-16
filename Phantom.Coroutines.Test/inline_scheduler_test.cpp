#include "Phantom.Coroutines/inline_scheduler.h"

using namespace Phantom::Coroutines;
using namespace Phantom::Coroutines::detail;

static_assert(scheduler<inline_scheduler>);
