#ifndef PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#define PHANTOM_COROUTINES_INCLUDE_TYPE_TRAITS_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <coroutine>
#include <functional>
#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>
#include "detail/config.h"
#include "detail/coroutine.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename...
> constexpr bool always_false = false;

// Determine if a given type is an instantiation of a template
// accepting type arguments.
template<
    typename T,
    template <typename ...> typename Template
> constexpr bool is_template_instantiation_v = false;

template<
    typename... Args,
    template <typename ...> typename Template
> constexpr bool is_template_instantiation_v<
    Template<Args...>,
    Template
> = true;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    template <typename ...> typename Template
> concept is_template_instantiation = is_template_instantiation_v<std::remove_cvref_t<T>, Template>;

// Determine if a given type is a derived class of an instantiation of
// a template accepting type arguments.
template<
    template<typename...> typename Template
> struct derived_instantiation_detector
{
    template<
        typename... Args
    > static void detect(
        const Template<Args...>&);
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    template<typename...> typename Template
> concept is_derived_instantiation = requires (T t)
{
    { derived_instantiation_detector<Template>::detect(t) };
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    typename...TTypes
> concept is_in_types = (std::is_same_v<T, TTypes> || ...);

template<
    typename T
> concept Label =
std::is_empty_v<T>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    template<typename> typename Filter,
    is_template_instantiation<std::tuple> TypesTuple,
    is_template_instantiation<std::tuple> FilteredTypesTuple = std::tuple<>
> struct filter_tuple_types;

template<
    template<typename> typename Filter,
    typename FilteredTypesTuple
> struct filter_tuple_types<
    Filter,
    std::tuple<>,
    FilteredTypesTuple
>
{
    typedef FilteredTypesTuple tuple_type;
};

template<
    template<typename> typename Filter,
    typename Type,
    typename... RemainingTypes,
    typename... FilteredTypes
> struct filter_tuple_types<
    Filter,
    std::tuple<Type, RemainingTypes...>,
    std::tuple<FilteredTypes...>>
    :
    public std::conditional_t<
    Filter<Type>::value,
    filter_tuple_types<Filter, std::tuple<RemainingTypes...>, std::tuple<FilteredTypes..., Type>>,
    filter_tuple_types<Filter, std::tuple<RemainingTypes...>, std::tuple<FilteredTypes...>>
    >
{
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    template<typename> typename Filter,
    typename...Types
> struct filter_types
{
    typedef typename filter_tuple_types<Filter, std::tuple<Types...>, std::tuple<>>::tuple_type tuple_type;
};

// Determine if a tuple contains a given element type.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Type,
    typename Tuple
>
constexpr bool tuple_has_element_v = false;

template<
    typename Type,
    typename ... RemainingElements
>
constexpr bool tuple_has_element_v<
    Type,
    std::tuple<Type, RemainingElements...>>
    = true;

template<
    typename Type,
    typename OtherType,
    typename ... RemainingElements
>
constexpr bool tuple_has_element_v<
    Type,
    std::tuple<OtherType, RemainingElements...>>
    = tuple_has_element_v<Type, std::tuple<RemainingElements...>>;

template<
    is_template_instantiation<std::tuple> ... Tuples
> struct tuple_cat_types
{
    static_assert(sizeof...(Tuples) == 0);
    typedef std::tuple<> tuple_type;
};

template<
    typename ... Types
> struct tuple_cat_types<
    std::tuple<Types...>
>
{
    typedef std::tuple<Types...> tuple_type;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Tuples
> using tuple_cat_types_t = typename tuple_cat_types<Tuples...>::tuple_type;

template<
    typename... Types1,
    typename... Types2,
    typename... Tuples
> struct tuple_cat_types<
    std::tuple<Types1...>,
    std::tuple<Types2...>,
    Tuples...
>
{
    typedef tuple_cat_types_t<std::tuple<Types1..., Types2...>, Tuples...> tuple_type;
};

template<
    typename BoundType
> struct same_as_filter
{
    template<
        typename Type
    > using filter = std::is_same<BoundType, Type>;
};

// Locate the index of a Type in a Tuple,
// returning no valid index if the type is not present or is duplicated.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Type,
    typename Tuple,
    typename = void
>
struct tuple_element_index;

template<
    typename Type,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<Type, RemainingTypes...>,
    std::enable_if_t<tuple_has_element_v<Type, std::tuple<RemainingTypes...>>>
>
{
};

template<
    typename Type,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<Type, RemainingTypes...>,
    std::enable_if_t<!tuple_has_element_v<Type, std::tuple<RemainingTypes...>>>
>
{
    static const size_t value = 0;
};

template<
    typename Type,
    typename OtherType,
    typename...RemainingTypes
>
struct tuple_element_index<
    Type,
    std::tuple<OtherType, RemainingTypes...>,
    std::void_t<
    std::enable_if_t<!std::is_same_v<Type, OtherType>>,
    decltype(tuple_element_index<Type, std::tuple<RemainingTypes...>>::value)>
>
{
    static const size_t value =
        1
        +
        tuple_element_index<Type, std::tuple<RemainingTypes...>>::value;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Type,
    typename Tuple
> constexpr size_t tuple_element_index_v = tuple_element_index<Type, Tuple>::value;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T,
    typename Conflict
>
    requires std::is_class_v<std::remove_reference_t<T>>
struct conflict_detector
    :
    public std::remove_reference_t<T>,
    public Conflict
{
};

PHANTOM_COROUTINES_MODULE_EXPORT
struct has_await_suspend_conflicted_name
{
    using await_suspend = int;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Awaiter
> concept has_await_suspend = !requires
{
    typename conflict_detector<Awaiter, has_await_suspend_conflicted_name>::await_suspend;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> concept has_get_return_object_on_allocation_failure = requires
{
    { Promise::get_return_object_on_allocation_failure() };
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename CoroutineHandle = coroutine_handle<>
> concept has_void_await_suspend = requires (
    TAwaiter awaiter,
    CoroutineHandle continuation)
{
    { awaiter.await_suspend(continuation) } -> std::same_as<void>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename CoroutineHandle = coroutine_handle<>
> concept has_bool_await_suspend = requires (
    TAwaiter awaiter,
    CoroutineHandle continuation)
{
    { awaiter.await_suspend(continuation) } -> std::same_as<bool>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename CoroutineHandle = coroutine_handle<>
> concept has_symmetric_transfer_await_suspend = requires (
    TAwaiter awaiter,
    CoroutineHandle continuation)
{
    { awaiter.await_suspend(continuation) } -> std::convertible_to<coroutine_handle<>>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaiter,
    typename CoroutineHandle = coroutine_handle<>
>
concept is_awaiter =
    requires (
TAwaiter awaiter)
{
    { awaiter.await_ready() } -> std::same_as<bool>;
    { awaiter.await_resume() };
}
&& has_await_suspend<TAwaiter>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaitable
> concept has_co_await_member = requires(
    TAwaitable awaitable
    )
{
    { std::forward<TAwaitable>(awaitable).operator co_await() } -> is_awaiter;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaitable
> concept has_co_await_non_member = requires(
    TAwaitable awaitable
    )
{
    { operator co_await(std::forward(awaitable)) } -> is_awaiter;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAwaitable
> concept is_awaitable =
has_co_await_member<TAwaitable>
||
has_co_await_non_member<TAwaitable>
||
is_awaiter<TAwaitable>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    has_co_await_member CoAwaitMember
>
decltype(auto) get_awaiter(
    CoAwaitMember&& awaitable
)
{
    return std::forward<CoAwaitMember>(awaitable).operator co_await();
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    has_co_await_non_member CoAwaitNonMember
>
decltype(auto) get_awaiter(
    CoAwaitNonMember&& awaitable
)
{
    return operator co_await(std::forward<CoAwaitNonMember>(awaitable));
}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_awaiter Awaiter
>
decltype(auto) get_awaiter(
    Awaiter&& awaitable
)
{
    return std::forward<Awaiter>(awaitable);
}

template<
    typename T
> struct remove_rvalue_reference
{
    typedef T type;
};

template<
    typename T
> struct remove_rvalue_reference<T&&>
{
    typedef T type;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> using remove_rvalue_reference_t = typename remove_rvalue_reference<T>::type;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_awaitable Awaitable
> using awaiter_type = decltype(get_awaiter(std::declval<Awaitable>()));

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_awaitable TAwaitable
>
using awaitable_result_type_t = decltype(std::declval<awaiter_type<TAwaitable>>().await_resume());

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> constexpr bool is_optional = false;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> constexpr bool is_optional<std::optional<T>> = true;

struct has_await_transform_conflicted_name
{
    using await_transform = int;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> concept has_await_transform = !requires
{
    typename conflict_detector<Promise, has_await_transform_conflicted_name>::await_transform;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
> using has_await_transform_filter = std::bool_constant<has_await_transform<T>>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise,
    typename ... Awaiter
> concept has_await_transform_for = requires (Promise promise)
{
    { promise.await_transform(std::declval<Awaiter>()...) };
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> concept has_return_void = requires (Promise promise)
{
    promise.return_void();
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise,
    typename Awaiter
> concept has_return_void_for = requires (Promise promise, Awaiter awaiter)
{
    { promise.return_void(awaiter) };
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Continuation
> concept is_coroutine_handle = is_template_instantiation_v<Continuation, std::coroutine_handle>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Continuation
> concept is_continuation =
std::constructible_from<Continuation>
&& std::is_default_constructible_v<Continuation>
&& requires (Continuation c)
{
    { c.resume() };
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Owner,
    typename Value
> decltype(auto) forward_owned(
    std::type_identity_t<Value>&& value
) noexcept
{
    if constexpr (
        std::is_rvalue_reference_v<Value>)
    {
        return std::move(value);
    }
    else if constexpr (
        std::is_lvalue_reference_v<Owner>
        || std::is_lvalue_reference_v<Value>)
    {
        return static_cast<Value&>(value);
    }
    else
    {
        return std::move(value);
    }
}

// Conditionally inherit from one base or another.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    bool Condition,
    typename BaseTrue,
    typename BaseFalse
> class inherit_if : public BaseTrue
{
    using BaseTrue::BaseTrue;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename BaseTrue,
    typename BaseFalse
> class inherit_if<
    false,
    BaseTrue,
    BaseFalse
> : public BaseFalse
{
    using BaseFalse::BaseFalse;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Value
> class value_storage
{
    Value m_value;

public:
    value_storage() requires std::is_default_constructible_v<Value> {}

    value_storage(
        std::invocable<> auto&& invocable
    ) requires
        std::same_as<Value, std::invoke_result_t<decltype(invocable)>>
        :
        m_value { std::invoke(std::forward<decltype(invocable)>(invocable)) }
    {}

protected:
    decltype(auto) value()
    {
        return (m_value);
    }

    decltype(auto) value() const
    {
        return (m_value);
    }
};
}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::awaiter_type;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::awaitable_result_type_t;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_awaitable;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_awaiter;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::has_co_await_member;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::has_co_await_non_member;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::get_awaiter;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_coroutine_handle;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::is_continuation;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::has_return_void;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::has_await_transform;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::has_get_return_object_on_allocation_failure;

} // namespace Phantom::Coroutines
#endif
