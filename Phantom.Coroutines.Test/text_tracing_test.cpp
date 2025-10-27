#include "async_test.h"
#include "Phantom.Coroutines/detail/config_macros.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.text_tracing;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/text_tracing.h"
#endif

namespace Phantom::Coroutines::tracing
{



}
