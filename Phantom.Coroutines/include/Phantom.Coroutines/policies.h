#pragma once

#include<concepts>
#include"type_traits.h"

namespace Phantom::Coroutines
{

struct wait_is_cancellable;
struct wait_is_not_cancellable;
struct wait_is_not_destroyable;

template<
	typename T
> concept is_wait_cancellation_policy = detail::is_in_types<
	wait_is_cancellable,
	wait_is_cancellable,
	wait_is_not_destroyable
>;

template<
	typename T
> struct is_wait_cancellation_policy_selector :
	std::integral_constant<
		bool,
		is_wait_cancellation_policy<T>
	>
{};

template<
	typename ... Policies
> using select_wait_cancellation_policy = detail::select_policy_t<
	is_wait_cancellation_policy_selector,
	Policies...
>;

struct single_awaiter;
struct multiple_awaiters;

template<
	typename T
> concept is_awaiter_cardinality_policy = detail::is_in_types<
	single_awaiter,
	multiple_awaiters
>;

template<
	typename T
> struct is_awaiter_cardinality_policy_selector :
	std::integral_constant<
		bool,
		is_awaiter_cardinality_policy<T>
	>
{};

template<
	typename ... Policies
> using select_awaiter_cardinality_policy = detail::select_policy_t<
	is_awaiter_cardinality_policy_selector,
	Policies...
>;

struct throw_on_destroy;
struct noop_on_destroy;

template<
	typename T
> concept is_wait_result_on_destruction_policy = detail::is_in_types<
	throw_on_destroy,
	noop_on_destroy
>;

template<
	typename T
> struct is_wait_result_on_destruction_policy_selector:
	std::integral_constant<
		bool,
		is_wait_result_on_destruction_policy<T>
	>
{};

template<
	typename ... Policies
> using select_wait_result_on_destruction_policy = detail::select_policy_t<
	is_wait_result_on_destruction_policy_selector,
	Policies...
>;

template<
	typename T
> struct continuation_type
{
	using type = T;
};

using default_continuation_type = continuation_type<coroutine_handle<>>;

template<
	typename T
> concept is_continuation_type_policy = detail::is_template_instantiation_v<
	T,
	continuation_type
>;

template<
	typename T
> struct is_continuation_type_policy_selector :
	std::integral_constant<
		bool,
		is_continuation_type_policy<T>
	>
{};

template<
	typename ... Policies
> using select_continuation_type_policy = typename detail::select_policy_t<
	is_continuation_type_policy_selector,
	Policies...
>;

template<
	typename ... Policies
> using select_continuation_type = typename select_continuation_type_policy<Policies...>::type;

}
