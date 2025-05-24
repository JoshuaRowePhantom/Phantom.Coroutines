export module Phantom.Coroutines.Test.stateful_metaprogramming_test;
import Phantom.Coroutines.stateful_metaprogramming;

namespace Phantom::Coroutines::stateful_metaprogramming
{

export
struct stateful_metaprogramming_test_module_label {};

static_assert(write_state<stateful_metaprogramming_test_module_label, int>);

}
