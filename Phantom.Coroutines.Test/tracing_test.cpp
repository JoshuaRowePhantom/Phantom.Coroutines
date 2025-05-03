#include <gtest/gtest.h>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.tracing;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#endif

namespace Phantom::Coroutines
{

struct tracing_test
{

};

}