#include <concepts>
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.function_traits;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/function_traits.h"
#endif

namespace Phantom::Coroutines
{

namespace
{
static_assert(std::same_as<function_traits<char(int, long)>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long)>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(!function_traits<char(int, long)>::is_noexcept);
static_assert(!function_traits<char(int, long)>::is_const);
static_assert(!function_traits<char(int, long)>::is_volatile);
static_assert(!function_traits<char(int, long)>::is_lvalue_ref_qualified);
static_assert(!function_traits<char(int, long)>::is_rvalue_ref_qualified);

static_assert(std::same_as<function_traits<char(int, long) noexcept>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long) noexcept>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(function_traits<char(int, long) noexcept>::is_noexcept);
static_assert(!function_traits<char(int, long) noexcept>::is_const);
static_assert(!function_traits<char(int, long) noexcept>::is_volatile);
static_assert(!function_traits<char(int, long) noexcept>::is_lvalue_ref_qualified);
static_assert(!function_traits<char(int, long) noexcept>::is_rvalue_ref_qualified);

static_assert(std::same_as<function_traits<char(int, long) const>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long) const>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(!function_traits<char(int, long) const>::is_noexcept);
static_assert(function_traits<char(int, long) const>::is_const);
static_assert(!function_traits<char(int, long) const>::is_volatile);
static_assert(!function_traits<char(int, long) const>::is_lvalue_ref_qualified);
static_assert(!function_traits<char(int, long) const>::is_rvalue_ref_qualified);

static_assert(std::same_as<function_traits<char(int, long) volatile>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long) volatile>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(!function_traits<char(int, long) volatile>::is_noexcept);
static_assert(!function_traits<char(int, long) volatile>::is_const);
static_assert(function_traits<char(int, long) volatile>::is_volatile);
static_assert(!function_traits<char(int, long) volatile>::is_lvalue_ref_qualified);
static_assert(!function_traits<char(int, long) volatile>::is_rvalue_ref_qualified);

static_assert(std::same_as<function_traits<char(int, long) &>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long) &>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(!function_traits<char(int, long)&>::is_noexcept);
static_assert(!function_traits<char(int, long)&>::is_const);
static_assert(!function_traits<char(int, long)&>::is_volatile);
static_assert(function_traits<char(int, long)&>::is_lvalue_ref_qualified);
static_assert(!function_traits<char(int, long)&>::is_rvalue_ref_qualified);

static_assert(std::same_as<function_traits<char(int, long) &&>::return_type, char>);
static_assert(std::same_as<function_traits<char(int, long) &&>::arguments_tuple_type, std::tuple<int, long>>);
static_assert(!function_traits<char(int, long)&&>::is_noexcept);
static_assert(!function_traits<char(int, long)&&>::is_const);
static_assert(!function_traits<char(int, long)&&>::is_volatile);
static_assert(!function_traits<char(int, long)&&>::is_lvalue_ref_qualified);
static_assert(function_traits<char(int, long)&&>::is_rvalue_ref_qualified);

static_assert(!function_traits<char()>::is_function_pointer);
static_assert(!function_traits<char()>::is_member_function_pointer);

struct S;
void foo();

static_assert(function_traits<char (*)()>::is_function_pointer);
static_assert(!function_traits<char (*)()>::is_member_function_pointer);
static_assert(std::same_as<char, function_traits<char (*)()>::return_type>);

static_assert(!function_traits<void(S::*)()>::is_function_pointer);
static_assert(function_traits<void(S::*)()>::is_member_function_pointer);
static_assert(std::same_as<char, function_traits<char(S::*)() const>::return_type>);

}
}