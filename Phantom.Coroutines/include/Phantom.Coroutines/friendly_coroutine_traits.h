#ifndef PHANTOM_COROUTINES_INCLUDE_GENERATOR_H
#define PHANTOM_COROUTINES_INCLUDE_GENERATOR_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include "Phantom.Coroutines/detail/config_macros.h"
#include "Phantom.Coroutines/detail/coroutine.h"
#include "Phantom.Coroutines/stateful_metaprogramming.h"
#include "detail/immovable_object.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{

namespace detail
{

struct no_traits {};

struct friendly_coroutine_traits_types_list {};

template<
    template<typename, typename ...> typename TraitsType
>
struct friendly_coroutine_traits_type_list_entry
{
    template<typename Result, typename ... Args>
    using traits_template = TraitsType<Result, Args...>;
};

static_assert(
    stateful_metaprogramming::initialize_list<
        friendly_coroutine_traits_types_list,
        stateful_metaprogramming::type_list<>
>);

template<
    typename FilteredTraits,
    typename Result,
    typename ... Args
>
consteval bool assert_no_conflicting_coroutine_traits()
{
    static_assert(
        FilteredTraits::size() < 2,
        "There are conflicting friendly traits. "
        "Please ensure that only one coroutine_traits specialization is used for the given Result and Args types."
        );
    return true;
}

template<
    typename Result,
    typename ... Args
>
consteval auto get_friendly_coroutine_traits_type()
{
    using friendly_coroutine_traits_type_list = stateful_metaprogramming::read_variable<
        detail::friendly_coroutine_traits_types_list,
        stateful_metaprogramming::type_list<Result, Args...>{}
    >;

    using filtered_coroutine_traits_type_list = stateful_metaprogramming::type_list_filter
    <
        []<typename ListEntry>(stateful_metaprogramming::type_list<ListEntry>)
    {
        if constexpr (requires
        {
            typename ListEntry::template traits_template<Result, Args...>::promise_type;
        })
        {
            return true;
        }
        else
        {
            return false;
        }
    },
        friendly_coroutine_traits_type_list
    > ;

    static_assert(
        assert_no_conflicting_coroutine_traits<
            filtered_coroutine_traits_type_list,
            Result,
            Args...
        >());

    if constexpr (filtered_coroutine_traits_type_list::size() == 0)
    {
        return no_traits{};
    }
    else
    {
        return stateful_metaprogramming::type_list_get<0, filtered_coroutine_traits_type_list>{};
    }
}


template<
    typename Result,
    typename ... Args
>
concept has_friend_coroutine_traits_function = requires
(Result result, Args... args)
{
    typename decltype(friend_coroutine_traits(result, args...))::promise_type;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    typename ... Args
>
using friendly_coroutine_traits_type =
decltype(get_friendly_coroutine_traits_type<Result, Args...>())::template traits_template<Result, Args...>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    typename ... Args
>
concept has_friendly_coroutine_traits =
!std::same_as<
    friendly_coroutine_traits_type<Result, Args...>,
    detail::no_traits
>;

} // namespace detail

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    template<typename, typename ...> typename TraitsType
>
constexpr bool add_coroutine_traits = 
    stateful_metaprogramming::append_list<
        detail::friendly_coroutine_traits_types_list,
        stateful_metaprogramming::type_list<detail::friendly_coroutine_traits_type_list_entry<TraitsType>>
    >;

} // namespace Phantom::Coroutines

namespace std
{
template<
    typename Result,
    typename ... Args
>
requires Phantom::Coroutines::detail::has_friendly_coroutine_traits<Result, Args...>
struct coroutine_traits<
    Result,
    Args...
>
    :
    Phantom::Coroutines::detail::friendly_coroutine_traits_type<Result, Args...>
{
};

template<
    typename Result,
    typename ... Args
>
    requires Phantom::Coroutines::detail::has_friend_coroutine_traits_function<Result, Args...>
struct coroutine_traits<
    Result,
    Args...
> :
    decltype(
        friend_coroutine_traits(
            std::declval<Result>(),
            std::declval<Args>()...
        )
    )
{
};

}

#endif
