#include <gtest/gtest.h>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.stateful_metaprogramming_test;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.stateful_metaprogramming;
import Phantom.Coroutines.Test.stateful_metaprogramming_test;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/stateful_metaprogramming.h"
#endif

namespace Phantom::Coroutines::stateful_metaprogramming
{

struct test_label {};
struct test_value {};
static_assert(!has_state<test_label>);
static_assert(write_state<test_label, test_value>);
static_assert(has_state<test_label>);
static_assert(std::same_as<test_value, read_state<test_label>>);

struct test_variable_label_1 {};
struct test_variable_label_2 {};

static_assert(initialize_variable<test_variable_label_1, value_list<1, 0>>);
static_assert(initialize_variable<test_variable_label_2, value_list<2, 0>>);
static_assert(std::same_as<value_list<1, 0>, read_variable<test_variable_label_1>>);
static_assert(std::same_as<value_list<2, 0>, read_variable<test_variable_label_2>>);
static_assert(write_variable<test_variable_label_1, value_list<1, 1>>);
static_assert(std::same_as<value_list<1, 1>, read_variable<test_variable_label_1>>);
static_assert(std::same_as<value_list<2, 0>, read_variable<test_variable_label_2>>);
static_assert(write_variable<test_variable_label_2, value_list<2, 1>>);
static_assert(std::same_as<value_list<1, 1>, read_variable<test_variable_label_1>>);
static_assert(std::same_as<value_list<2, 1>, read_variable<test_variable_label_2>>);
static_assert(write_variable<test_variable_label_1, value_list<1, 2>>);
static_assert(std::same_as<value_list<1, 2>, read_variable<test_variable_label_1>>);
static_assert(std::same_as<value_list<2, 1>, read_variable<test_variable_label_2>>);
static_assert(write_variable<test_variable_label_2, value_list<2, 2>>);
static_assert(std::same_as<value_list<1, 2>, read_variable<test_variable_label_1>>);
static_assert(std::same_as<value_list<2, 2>, read_variable<test_variable_label_2>>);

struct test_list_label_1 {};
static_assert(initialize_list<test_list_label_1, value_list<1, 2>>);
static_assert(append_list<test_list_label_1, value_list<3, 4>>);
static_assert(std::same_as<value_list<1, 2, 3, 4>, read_list<test_list_label_1>>);
static_assert(append_list<test_list_label_1, value_list<5, 6>>);
static_assert(std::same_as<value_list<1, 2, 3, 4, 5, 6>, read_list<test_list_label_1>>);
static_assert(append_list<test_list_label_1, value_list<7, 8>>);
static_assert(std::same_as<value_list<1, 2, 3, 4, 5, 6, 7, 8>, read_list<test_list_label_1>>);

#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE) || defined(PHANTOM_COROUTINES_TESTING_MODULES)
static_assert(has_state<stateful_metaprogramming_test_module_label>);
static_assert(std::same_as<int, read_state<stateful_metaprogramming_test_module_label>>);
#endif

}