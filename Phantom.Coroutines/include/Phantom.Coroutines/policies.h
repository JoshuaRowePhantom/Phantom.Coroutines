#pragma once

#include<concepts>
#include"type_traits.h"

namespace Phantom::Coroutines
{

struct concrete_policy {};

template<
	typename TPolicy,
	typename TBasePolicy
> concept is_concrete_policy =
std::is_base_of_v<TBasePolicy, TPolicy>
&&
std::is_base_of_v<concrete_policy, TPolicy>;

struct await_cancellation_policy {};
struct await_is_cancellable : public await_cancellation_policy, public concrete_policy {};
struct await_is_not_cancellable : public await_cancellation_policy, public concrete_policy {};

template<
	typename T
> concept is_await_cancellation_policy =
is_concrete_policy<T, await_cancellation_policy>;

template<
	typename T
> struct is_await_cancellation_policy_selector :
	std::integral_constant<
		bool,
		is_await_cancellation_policy<T>
	>
{};

template<
	typename ... Policies
> using select_await_cancellation_policy = detail::select_policy_t<
	is_await_cancellation_policy_selector,
	Policies...
>;

struct awaiter_cardinality_policy {};
struct single_awaiter : public awaiter_cardinality_policy, public concrete_policy {};
struct multiple_awaiters : public awaiter_cardinality_policy, public concrete_policy {};

template<
	typename T
> concept is_awaiter_cardinality_policy = 
is_concrete_policy<
	T,
	awaiter_cardinality_policy
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

struct await_result_on_destruction_policy {};
struct throw_on_destroy : public await_result_on_destruction_policy, public concrete_policy {};
struct noop_on_destroy : public await_result_on_destruction_policy, public concrete_policy {};
struct fail_on_destroy_with_awaiters : public await_result_on_destruction_policy, public concrete_policy {};

template<
	typename T
> concept is_await_result_on_destruction_policy =
is_concrete_policy<
	T,
	await_result_on_destruction_policy
>;

template<
	typename T
> struct is_await_result_on_destruction_policy_selector:
	std::integral_constant<
		bool,
		is_await_result_on_destruction_policy<T>
	>
{};

template<
	typename ... Policies
> using select_await_result_on_destruction_policy = detail::select_policy_t<
	is_await_result_on_destruction_policy_selector,
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

struct use_after_join_policy {};
struct throw_on_use_after_join : use_after_join_policy, concrete_policy {};
struct fail_on_use_after_join : use_after_join_policy, concrete_policy {};
struct noop_on_use_after_join : use_after_join_policy, concrete_policy {};

template<
	typename T
> concept is_use_after_join_policy =
is_concrete_policy<T, use_after_join_policy>;

template<
	typename T
> struct is_use_after_join_policy_selector :
	std::integral_constant<
	bool,
	is_use_after_join_policy<T>
	>
{};

template<
	typename ... Policies
> using select_use_after_join_policy = detail::select_policy_t<
	is_use_after_join_policy_selector,
	Policies...
>;

}
