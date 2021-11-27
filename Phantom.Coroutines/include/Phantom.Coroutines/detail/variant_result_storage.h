#pragma once
#include <type_traits>
#include <variant>

namespace Phantom::Coroutines::detail
{
template<
	typename T
> struct variant_result_storage
{
	static constexpr bool is_void = false;
	static constexpr bool is_reference = false;
	static constexpr bool is_lvalue_reference = false;
	static constexpr bool is_rvalue_reference = false;
	typedef T result_variant_member_type;
};

template<
> struct variant_result_storage<
	void
>
{
	static constexpr bool is_void = true;
	static constexpr bool is_reference = false;
	static constexpr bool is_lvalue_reference = false;
	static constexpr bool is_rvalue_reference = false;
	typedef std::monostate result_variant_member_type;
};

template<
	typename T
> struct variant_result_storage<
	T&
>
{
	static constexpr bool is_void = false;
	static constexpr bool is_reference = true;
	static constexpr bool is_lvalue_reference = true;
	static constexpr bool is_rvalue_reference = false;
	typedef std::reference_wrapper<T> result_variant_member_type;
};

template<
	typename T
> struct variant_result_storage<
	T&&
>
{
	static constexpr bool is_void = false;
	static constexpr bool is_reference = true;
	static constexpr bool is_lvalue_reference = false;
	static constexpr bool is_rvalue_reference = true;
	typedef std::reference_wrapper<T> result_variant_member_type;
};

}