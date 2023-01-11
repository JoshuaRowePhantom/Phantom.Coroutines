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

template<
    typename BasePolicy
> struct policy_selector
{
    template<
        typename T
    > static constexpr bool is_policy = is_concrete_policy<T, BasePolicy>;
};

namespace detail
{
template<
    typename PolicySelector,
    typename ... Policies
> struct select_policy_impl
{
    static_assert(detail::always_false<PolicySelector>, "Policy list does not contain desired policy.");
};

template<
    typename PolicySelector,
    typename MatchingPolicy,
    typename ... Policies
>
    requires (PolicySelector::template is_policy<MatchingPolicy>)
struct select_policy_impl<
    PolicySelector,
    MatchingPolicy,
    Policies...
>
{
    using type = MatchingPolicy;
};

template<
    typename PolicySelector,
    typename NotMatchingPolicy,
    typename ... Policies
>
    requires (!PolicySelector::template is_policy<NotMatchingPolicy>)
struct select_policy_impl<
    PolicySelector,
    NotMatchingPolicy,
    Policies...
> : public select_policy_impl<PolicySelector, Policies...>
{
};

}

template<
    typename PolicySelector,
    typename ... Policies
> using select_policy = typename detail::select_policy_impl<PolicySelector, Policies...>::type;


struct await_cancellation_policy {};
struct await_is_cancellable : public await_cancellation_policy, public concrete_policy {};
struct await_is_not_cancellable : public await_cancellation_policy, public concrete_policy {};

template<
    typename T
> concept is_await_cancellation_policy =
is_concrete_policy<T, await_cancellation_policy>;

template<
    typename ... Policies
> using select_await_cancellation_policy = select_policy<
    policy_selector<await_cancellation_policy>,
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
    typename ... Policies
> using select_awaiter_cardinality_policy = select_policy<
    policy_selector<awaiter_cardinality_policy>,
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
    typename ... Policies
> using select_await_result_on_destruction_policy = select_policy<
    policy_selector<await_result_on_destruction_policy>,
    Policies...
>;

template<
    typename T = void
> struct continuation_type : 
    concrete_policy,
    continuation_type<>
{
    using type = T;
};

template<> struct continuation_type<void>
{};

using default_continuation_type = continuation_type<coroutine_handle<>>;

template<
    typename T
> concept is_continuation_type_policy = is_concrete_policy<T, continuation_type<>>;

template<
    typename ... Policies
> using select_continuation_type_policy = select_policy<
    policy_selector<continuation_type<>>,
    Policies...
>;

template<
    typename ... Policies
> using select_continuation_type = typename select_continuation_type_policy<Policies...>::type;

struct use_after_join_policy {};
struct throw_on_use_after_join : use_after_join_policy, concrete_policy {};
struct fail_on_use_after_join : use_after_join_policy, concrete_policy {};

template<
    typename T
> concept is_use_after_join_policy =
is_concrete_policy<T, use_after_join_policy>;

template<
    typename ... Policies
> using select_use_after_join_policy = select_policy<
    policy_selector<use_after_join_policy>,
    Policies...
>;

template<
    typename T = void
> struct base_promise_type
    : 
    concrete_policy,
    base_promise_type<>
{
    using type = T;
};

template<>
struct base_promise_type<void>
{};

template<
    typename T
> concept is_base_promise_type =
is_concrete_policy<T, base_promise_type<>>;

template<
    typename ... Policies
> using select_base_promise_type_policy = select_policy<
    policy_selector<base_promise_type<>>,
    Policies...
>;

template<
    typename ... Policies
> using select_base_promise_type = typename select_base_promise_type_policy<Policies...>::type;

}
