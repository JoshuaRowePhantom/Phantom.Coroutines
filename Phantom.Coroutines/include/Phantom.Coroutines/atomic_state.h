#pragma once
#include <assert.h>
#include <bit>
#include <optional>
#include <type_traits>
#include "detail/coroutine.h"
#include "detail/type_traits.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TLabel
> class SingletonState
{
public:
    typedef TLabel Label;

    SingletonState(
        TLabel label = TLabel()
    ) {}
};

template<
    typename TStateSetType, 
    typename TRepresentation
> struct StateSetTraits;

template<
    // A label for the type of state being stored.
    typename TLabel,
    // The type of state object being stored.
    typename TStateSetType,
    // The traits for converting a state object value to an underlying representation and back.
    template<
        typename TStateSetType, 
        typename TRepresentation
    > typename TStateSetTraits = StateSetTraits
> class StateSet
{
public:
    typedef TLabel Label;
    typedef TStateSetType element_type;
    
    // This object is not constructible.
    StateSet() = delete; 
};

template<
    typename TLabel,
    typename TStateSetType
> class StateSetElement
{
    TStateSetType m_element;

public:
    StateSetElement(
        TStateSetType element
    ) : m_element(
        element)
    {}

    operator TStateSetType() const
    {
        return m_element;
    }
};

// This StateSetTraits allows an arbitrary type TPointerToValue to be
// represented as a void* in an AtomicState.
template<
    typename TPointedToValue
> struct StateSetTraits<TPointedToValue*, void*>
{
    static constexpr size_t align_of()
    {
        return alignof(TPointedToValue);
    }

    static constexpr void* to_representation(
        TPointedToValue* value
    )
    {
        return value;
    }

    static constexpr TPointedToValue* from_representation(
        void* representation)
    {
        return static_cast<TPointedToValue>(
            representation);
    }
};

// This StateSetTraits allows a coroutine_handle<T> to be
// represented as a void* in an AtomicState.
template<
    typename TPromise
> struct StateSetTraits<coroutine_handle<TPromise>, void*>
{
    constexpr size_t align_of()
    {
        return alignof(coroutine_handle<TPromise>);
    }

    constexpr void* to_representation(
        coroutine_handle<TPromise> value
    )
    {
        return value.address();
    }

    constexpr coroutine_handle<TPromise> from_representation(
        void* representation)
    {
        return coroutine_handle<TPromise>::from_address(
            representation);
    }
};

template<
    typename...T
> struct atomic_state_handler_tag {};

template<
    typename TRepresentation,
    typename TStateType
> class SingletonStateHandler;

template<
    typename TLabel
> class SingletonStateHandler<
    void*, 
    SingletonState<TLabel>
>
{
    static inline std::max_align_t g_objectWithUniqueAddressValue;

protected:
    static bool is_state(
        void* representation,
        atomic_state_handler_tag<SingletonState<TLabel>>)
    {
        return representation == &g_objectWithUniqueAddressValue;
    }

    static void* to_representation(
        SingletonState<TLabel>
    )
    {
        return &g_objectWithUniqueAddressValue;
    }
};

template<
    typename TRepresentation,
    typename TStateSet,
    size_t StateSetIndex,
    uintptr_t RepresentationPointerMask
> class StateSetHandler;

template<
    typename TLabel,
    typename TStateSetType,
    template <typename, typename> typename TStateSetTraits,
    size_t StateSetIndex,
    uintptr_t StateSetIndexPointerMask
> class StateSetHandler<
    void*,
    StateSet<
        TLabel, 
        TStateSetType,
        TStateSetTraits
    >, 
    StateSetIndex,
    StateSetIndexPointerMask
>
{
    static const uintptr_t c_StateSetIndexPointerMask = StateSetIndexPointerMask;

    static_assert(
        c_StateSetIndexPointerMask < alignof(TStateSetType),
        "The alignment of the TStateSetType is too small to allow storing in the low order bits of a pointer.");

    typedef TStateSetTraits<TStateSetType, void*> state_set_traits;

protected:
    static bool is_state(
        void* representation,
        atomic_state_handler_tag<TLabel>)
    {
        return reinterpret_cast<uintptr_t>(representation) & StateSetIndexPointerMask == StateSetIndex;
    }

    static void* to_representation(
        StateSetElement<TLabel, TStateSetType> element
    )
    {
        return to_representation(
            element,
            atomic_state_handler_tag<TLabel>()
        );
    }

    static void* to_representation(
        TStateSetType state,
        atomic_state_handler_tag<TLabel>
    )
    {
        auto statePointer = state_set_traits::to_representation(
            state);
        
        auto stateUint = reinterpret_cast<uint64_t>(
            statePointer);
        
        // Can only pass aligned pointers to StateSetHandle!
        assert(
            (stateUint & c_StateSetIndexPointerMask) == 0);

        auto stateUintWithSetNumber = stateUint | StateSetIndex;

        // Internal error, too few bits in StateSetIndexPointerMask.
        assert(
            (stateUintWithSetNumber & ~c_StateSetIndexPointerMask) == stateUint);

        return reinterpret_cast<void*>(
            stateUintWithSetNumber);
    }

    static TStateSetType from_representation(
        void* representation,
        atomic_state_handler_tag<TLabel>
    )
    {
        auto stateUintWithSetNumber = reinterpret_cast<uint64_t>(
            representation);

        // Can't convert wrong representation type to value!
        assert(
            stateUintWithSetNumber & StateSetIndexPointerMask == StateSetIndex);

        auto stateUint = stateUintWithSetNumber & StateSetIndexPointerMask;

        auto statePointer = reinterpret_cast<void*>(
            stateUintWithSetNumber);

        return state_set_traits::from_representation(
            statePointer);
    }
};

// Determine if a state type is a singleton state.
template<
    typename TSingletonState
> constexpr bool IsSingletonState = false;

template<
    typename TLabel
> constexpr bool IsSingletonState<SingletonState<TLabel>> = true;

template<
    typename TState
> struct IsSingletonStateFilter : std::bool_constant<IsSingletonState<TState>>{};

// Determine if a state type is a set type.
template<
    typename TStateSet
> constexpr bool IsStateSet = false;

template<
    typename TLabel,
    typename TStateSetType,
    template<typename, typename> typename TStateSetTraits
> constexpr bool IsStateSet<StateSet<TLabel, TStateSetType, TStateSetTraits>> = true;

template<
    typename TState
> struct IsStateSetFilter : std::bool_constant<IsStateSet<TState>> {};

template<
    typename TStateType
> concept StateType =
IsSingletonState<TStateType>
||
IsStateSet<TStateType>;

template<
    typename TRepresentation,
    typename StateTypesTuple,
    typename SingletonStateTypesTuple = typename filter_tuple_types<IsSingletonStateFilter, StateTypesTuple>::tuple_type,
    typename StateSetTypesTuple = typename filter_tuple_types<IsStateSetFilter, StateTypesTuple>::tuple_type,
    typename StateSetTypesIndexSequence = std::make_index_sequence<std::tuple_size_v<StateSetTypesTuple>>,
    uintptr_t RepresentationPointerMask = (1 << std::bit_width(std::tuple_size_v<StateSetTypesTuple>)) - 1
>
class BasicAtomicStateHandlers;

template<
    typename TRepresentation,
    typename... StateTypes,
    typename... SingletonStateTypes,
    typename... StateSetTypes,
    size_t... StateSetIndices,
    uintptr_t RepresentationPointerMask
>
class BasicAtomicStateHandlers<
    TRepresentation,
    std::tuple<StateTypes...>,
    std::tuple<SingletonStateTypes...>,
    std::tuple<StateSetTypes...>,
    std::integer_sequence<size_t, StateSetIndices...>,
    RepresentationPointerMask
>
    :
public SingletonStateHandler<
    TRepresentation,
    SingletonStateTypes
>...,

public StateSetHandler<
    TRepresentation,
    StateSetTypes,
    StateSetIndices,
    RepresentationPointerMask
>...
{
protected:
    typedef std::tuple<
        typename StateSetTypes::Label...
    > StateSetTypeLabelsTuple;

    typedef std::tuple<
        typename StateSetTypes::element_type...
    > StateSetElementTypesTuple;

    using SingletonStateHandler<
        TRepresentation,
        SingletonStateTypes
    >::to_representation...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        RepresentationPointerMask
    >::from_representation...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        RepresentationPointerMask
    >::to_representation...;

    static bool is_singleton(
        TRepresentation representation)
    {
        return (SingletonStateHandler<TRepresentation, SingletonStateTypes>::is_state(
            representation,
            atomic_state_handler_tag<SingletonStateTypes>()) || ...);
    }
};


template<
    typename TAtomicState,
    typename TStateType = void
> class state;

template<
    typename TRepresentation,
    StateType...TStateTypes
> class basic_atomic_state
    :
BasicAtomicStateHandlers<
    TRepresentation,
    std::tuple<TStateTypes...>
>
{
    template<
        typename TAtomicState,
        typename TStateType
    > friend class state;

    std::atomic<TRepresentation> m_state;

public:
    template<
        typename TStateType = void
    > using state_type = state<basic_atomic_state, TStateType>;

    // Allow initialization from a state type
    basic_atomic_state(
        state_type<> value
    ) : m_state(
        value.m_value
    ){}

    // Allow initialization from a SingletonState directly.
    template<
        typename TLabel
    > basic_atomic_state(
        SingletonState<TLabel> state
    ) : basic_atomic_state(
        state_type<>(state))
    {}

    // Allow initialization from a label directly.
    template<
        Label TLabel
    > basic_atomic_state(
        TLabel state
    ) : basic_atomic_state(
        SingletonState<TLabel>())
    {}

    void store(
        state_type<> value,
        std::memory_order order = std::memory_order_seq_cst
    )
    {
        m_state.store(
            value.m_value,
            order);
    }

    state_type<> load(
        std::memory_order order = std::memory_order_seq_cst
    )
    {
        return state_type<>(m_state.load(order));
    }
};

template<
    typename...TStateTypes
> using atomic_state = basic_atomic_state<void*, TStateTypes...>;

// This represents a concrete generic state.
// It comparable to other states via implicit conversions to this type.
// It can be conditionally converted to a concrete non-singleton state.
template<
    typename TRepresentation,
    typename...TStateTypes
> class state<
    basic_atomic_state<TRepresentation, TStateTypes...>,
    void
>
{
    // Allow basic_atomic_state access to private members.
    template<
        typename TRepresentation,
        StateType...TStateTypes
    > friend class basic_atomic_state;

    // Allow other state<> specializations access to private members.
    template<
        typename TAtomicState,
        typename TStateType
    > friend class state;

    typedef basic_atomic_state<TRepresentation, TStateTypes...> atomic_state;

    TRepresentation m_value;

    explicit state(
        TRepresentation value
    ) : m_value(
        value)
    {}

public:
    // Allow implicit construction from anything that has
    // a to_representation method.
    template<
        typename ElementType
    > requires requires(ElementType element)
    {
        { atomic_state::to_representation(
            element
        ) } -> std::convertible_to<TRepresentation>;
    }
    state(
        ElementType elementType
    ) : m_value(
        atomic_state::to_representation(
            elementType))
    {}

    constexpr bool operator==(
        const state& other
        ) const
    {
        return m_value == other.m_value;
    }

    constexpr bool operator!=(
        const state& other
        ) const
    {
        return m_value != other.m_value;
    }

    constexpr bool is_singleton() const
    {
        return atomic_state::is_singleton(
            m_value);
    }
};

// This represents a concrete singleton state.
// It is constructible and convertible to the generic state.
template<
    typename TRepresentation,
    typename...TStateTypes,
    typename TLabel
>
requires is_in_types<SingletonState<TLabel>, TStateTypes...>
class state<
    basic_atomic_state<TRepresentation, TStateTypes...>,
    SingletonState<TLabel>
>
{
    typedef basic_atomic_state<TRepresentation, TStateTypes...> atomic_state;
    typedef state<atomic_state> VoidState;

public:
    state()
    {}

    // Allow implicit conversion to State<AtomicState>.
    operator VoidState() const
    {
        return VoidState(
            atomic_state::to_representation(*this));
    }
};

// This represents a concrete element from a state set.
// It is constructible and convertible to the generic state.
template<
    typename...TStateTypes,
    typename TRepresentation,
    typename TLabel,
    typename TStateSetType,
    template<typename, typename> typename TStateSetTraitsType
> 
requires is_in_types<
    StateSet<
        TLabel,
        TStateSetType,
        TStateSetTraitsType
    >,
    TStateTypes...
>
class state<
    basic_atomic_state<TRepresentation, TStateTypes...>,
    StateSet<
        TLabel,
        TStateSetType,
        TStateSetTraitsType
    >
>
{
    typedef basic_atomic_state<void*, TStateTypes...> atomic_state;
    typedef state<atomic_state> VoidState;

    TRepresentation m_value;

public:
    state(
        TStateSetType value)
    : m_value(
        atomic_state::to_representation(
            value,
            atomic_state_handler_tag<TLabel>()))
    {}

    // Allow implicit conversion to State<AtomicState>.
    operator VoidState() const
    {
        return VoidState(m_value);
    }

    operator TStateSetType () const
    {
        return atomic_state::from_representation(
            m_value,
            atomic_state_handler_tag<TLabel>()
        );
    }
};

}

using detail::SingletonState;
using detail::StateSet;
using detail::StateSetTraits;
using detail::basic_atomic_state;
using detail::atomic_state;
using detail::state;

}
