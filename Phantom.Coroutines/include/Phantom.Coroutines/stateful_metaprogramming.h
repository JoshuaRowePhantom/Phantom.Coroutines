#ifndef PHANTOM_COROUTINES_INCLUDE_STATEFUL_METAPROGRAMMING_H
#define PHANTOM_COROUTINES_INCLUDE_STATEFUL_METAPROGRAMMING_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "Phantom.Coroutines/detail/config_macros.h"
#include <tuple>
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines::stateful_metaprogramming
{

namespace detail
{

template<
    typename Label
>
struct state_reader
{
    friend auto StateFunction(state_reader);
};

template<
    typename Label,
    typename Value
>
struct state_writer
{
    friend auto StateFunction(state_reader<Label>)
    {
        return Value{};
    }

    consteval operator bool() const
    {
        return true;
    }
};

}

// State is one-time settable state
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value
>
constexpr bool write_state = detail::state_writer<Label, Value>{};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
constexpr bool has_state = 
    requires (detail::state_reader<Label> label) { StateFunction(label); };

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
using read_state = decltype(StateFunction(detail::state_reader<Label>{}));

// Variables are modifyable state.
//.They must be initialized with initialize_variable
// and can then be read and written using write_variable and read_variable.
namespace detail
{

// Used for representing variables
template<
    typename Label,
    size_t Index
>
struct variable_label
{
    static constexpr size_t index = Index;

    static consteval variable_label<Label, Index + 1> next()
    {
        return {};
    }
};

template<
    typename Label,
    size_t LowIndex,
    size_t HighIndex,
    auto EvalTag
>
consteval auto get_current_variable_label()
{
    if constexpr (has_state<variable_label<Label, HighIndex>, EvalTag>)
    {
        // Begin by searching upward, doubling the High index each time.
        return get_current_variable_label<Label, HighIndex, HighIndex * 2, EvalTag>();
    }
    else if constexpr (LowIndex + 1 == HighIndex)
    {
        // We've narrowed down to the index containing the data.
        return variable_label<Label, LowIndex>{};
    }
    else if constexpr (has_state<variable_label<Label, (LowIndex + HighIndex) / 2>, EvalTag>)
    { 
        // The upper half of the index range contains the value to read.
        return get_current_variable_label<Label, (LowIndex + HighIndex) / 2, HighIndex, EvalTag>();
    }
    else
    {
        // The lower half of the index range contains the value to read.
        return get_current_variable_label<Label, LowIndex, (LowIndex + HighIndex) / 2, EvalTag>();
    }
}

}

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value
>
constexpr bool initialize_variable = detail::state_writer<
    detail::variable_label<Label, 0>,
    Value
>{};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename Value,
    auto EvalTag = [] {}
>
constexpr bool write_variable = write_state<
    decltype(detail::get_current_variable_label<Label, 0, 1, EvalTag>().next()),
    Value
>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
using read_variable = read_state<decltype(detail::get_current_variable_label<Label, 0, 1, EvalTag>()), EvalTag>;

// Used to represent arbitrary type lists.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename ... Types
> struct type_list
{
    using tuple_type = std::tuple<Types...>;

    static consteval auto make_tuple()
    {
        return std::make_tuple(Types{}...);
    }

    template<
        typename ... OtherTypes
    >
    consteval auto append(type_list<OtherTypes...>) const
    {
        return type_list<Types..., OtherTypes...>{};
    }

    static constexpr size_t size()
    {
        return sizeof...(Types);
    }

    template<
        typename ... OtherTypes
    >
    bool operator==(type_list<OtherTypes...>) const
    {
        return false;
    }

    template<
        typename ... OtherTypes
    >
    bool operator!=(type_list<OtherTypes...>) const
    {
        return true;
    }

    bool operator==(type_list) const
    {
        return true;
    }

    bool operator!=(type_list) const
    {
        return false;
    }

    //template<
    //    auto predicate
    //>
    //auto filter(
    //) const
    //{
    //    auto applyToElement = [&](auto element)
    //    {
    //        if constexpr (predicate(element))
    //        {
    //            return element{};
    //        }
    //        else
    //        {
    //            return type_list<>;
    //        }
    //    };


    //}
};

type_list<> type_list_concat()
{
    return {};
}

auto type_list_concat(
    auto list
)
{
    return list;
}

template<
    typename List1,
    typename List2,
    typename ... Lists
>
auto type_list_concat(
    List1 list1,
    List2 list2,
    Lists ... lists
)
{
    return type_list_concat(
        list1.append(list2),
        lists...);
}

// Used to represent arbitrary non-type value lists.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    auto ... Values
> struct value_list : type_list<decltype(Values)...>
{
    static consteval auto make_tuple()
    {
        return std::make_tuple(Values...);
    }

    template<
        auto ... OtherValues
    >
    consteval auto append(value_list<OtherValues...>) const
    {
        return value_list<Values..., OtherValues...>{};
    }

    template<
        auto ... OtherValues
    >
    bool operator==(value_list<OtherValues...>) const
    {
        return false;
    }

    template<
        auto ... OtherValues
    >
    bool operator!=(value_list<OtherValues...>) const
    {
        return true;
    }

    bool operator==(value_list) const
    {
        return true;
    }

    bool operator!=(value_list) const
    {
        return false;
    }
};

// Manipulate lists.
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename List
>
constexpr bool initialize_list = initialize_variable<Label, List>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    auto EvalTag = [] {}
>
using read_list = read_variable<Label, EvalTag>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Label,
    typename List,
    auto EvalTag = [] {}
>
constexpr bool append_list = 
    write_variable<
        Label,
        decltype(read_variable<Label, EvalTag>{}.append(List{})),
    EvalTag
>;

}

#endif
