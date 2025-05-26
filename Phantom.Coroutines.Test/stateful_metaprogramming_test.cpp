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

static_assert(std::same_as<type_list<>, type_list_concatenate<>>);
static_assert(std::same_as<type_list<int>, type_list_concatenate<type_list<int>>>);
static_assert(std::same_as<type_list<int, bool>, type_list_concatenate<type_list<int>, type_list<bool>>>);
static_assert(std::same_as<type_list<int, long, bool, long, char, char>, type_list_concatenate<type_list<int, long>, type_list<bool, long>, type_list<char, char>>>);

static_assert(
    std::same_as<type_list<char, int>,
    type_list_filter<
        []<typename Type>(type_list<Type> element)
        {
            if constexpr (std::same_as<Type, bool>)
            {
                return false;
            }
            else
            {
                return true;
            }
        },
        type_list<bool, char, bool, int, bool>
    >
>);

}