#ifndef PHANTOM_COROUTINES_INCLUDE_ATOMIC_STATE_H
#define PHANTOM_COROUTINES_INCLUDE_ATOMIC_STATE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <atomic>
#include <assert.h>
#include <bit>
#include <cstddef>
#include <optional>
#include <tuple>
#include <type_traits>
#include "config.h"
#include "coroutine.h"
#include "Phantom.Coroutines/type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TLabel
> class SingletonState
{
public:
    typedef TLabel Label;
    static constexpr bool is_singleton = true;

    SingletonState(
        TLabel = TLabel()
    ) {}
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TStateSetType, 
    typename TRepresentation
> struct StateSetTraits;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    // A label for the type of state being stored.
    typename TLabel,
    // The type of state object being stored,
    // which may be the same as the label.
    typename TStateSetType = TLabel,
    // The traits for converting a state object value to an underlying representation and back.
    template<
        typename, 
        typename
    > typename TStateSetTraits = StateSetTraits
> class StateSet
{
public:
    typedef TLabel Label;
    typedef TStateSetType element_type;
    const bool is_singleton = false;

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
        TLabel label,
        TStateSetType element
    ) : m_element(
        element)
    {}

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
        return static_cast<TPointedToValue*>(
            representation);
    }
};

// This StateSetTraits allows a coroutine_handle<T> to be
// represented as a void* in an AtomicState.
template<
    typename TPromise
> struct StateSetTraits<coroutine_handle<TPromise>, void*>
{
    static constexpr size_t align_of()
    {
        return sizeof(uintptr_t);
    }

    static constexpr void* to_representation(
        coroutine_handle<TPromise> value
    )
    {
        return value.address();
    }

    static constexpr coroutine_handle<TPromise> from_representation(
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
>
class UniqueObject
{
protected:
    static inline std::max_align_t g_objectWithUniqueAddressValue;
};

template<
    typename TLabel
> class SingletonStateHandler<
    void*, 
    SingletonState<TLabel>
>
    :
private UniqueObject<TLabel>
{
    using UniqueObject<TLabel>::g_objectWithUniqueAddressValue;

protected:
    static constexpr bool is_singleton(
        atomic_state_handler_tag<TLabel>)
    {
        return true;
    }

    static bool is_state(
        void* representation,
        atomic_state_handler_tag<TLabel>)
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
    size_t StateSetSize
> class StateSetHandler;

template<
    typename TLabel,
    typename TStateSetType,
    template <typename, typename> typename TStateSetTraits,
    size_t StateSetIndex,
    size_t StateSetSize
> class StateSetHandler<
    void*,
    StateSet<
        TLabel, 
        TStateSetType,
        TStateSetTraits
    >, 
    StateSetIndex,
    StateSetSize
>
{
    static const uintptr_t c_StateSetIndex = StateSetIndex;
    static const uintptr_t c_StateSetIndexPointerMask = (1 << (std::bit_width(StateSetSize) - 1)) - 1;
    typedef TStateSetTraits<TStateSetType, void*> state_set_traits;

    static_assert(
        c_StateSetIndexPointerMask < state_set_traits::align_of(),
        "The alignment of the TStateSetType is too small to allow storing in the low order bits of a pointer.");

protected:
    static constexpr bool is_singleton(
        atomic_state_handler_tag<TLabel>)
    {
        return false;
    }

    static bool is_state(
        void* representation,
        atomic_state_handler_tag<TLabel>)
    {
        return (reinterpret_cast<uintptr_t>(representation) & c_StateSetIndexPointerMask) == c_StateSetIndex;
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
        
        auto stateUint = reinterpret_cast<uintptr_t>(
            statePointer);
        
        // Can only pass aligned pointers to StateSetHandle!
        assert(
            (stateUint & c_StateSetIndexPointerMask) == 0);

        auto stateUintWithSetNumber = stateUint | c_StateSetIndex;

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
        auto stateUintWithSetNumber = reinterpret_cast<uintptr_t>(
            representation);

        // Can't convert wrong representation type to value!
        assert(
            (stateUintWithSetNumber & c_StateSetIndexPointerMask) == StateSetIndex);

        auto stateUint = stateUintWithSetNumber & ~c_StateSetIndexPointerMask;

        auto statePointer = reinterpret_cast<void*>(
            stateUint);

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
    typename StateSetTypesIndexSequence = std::make_index_sequence<std::tuple_size_v<StateSetTypesTuple>>
>
class BasicAtomicStateHandlers;

template<
    typename TRepresentation,
    typename... StateTypes,
    typename... SingletonStateTypes,
    typename... StateSetTypes,
    size_t... StateSetIndices
>
class BasicAtomicStateHandlers<
    TRepresentation,
    std::tuple<StateTypes...>,
    std::tuple<SingletonStateTypes...>,
    std::tuple<StateSetTypes...>,
    std::integer_sequence<size_t, StateSetIndices...>
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
        sizeof...(StateSetIndices)
    >...
{
public:
    typedef std::tuple<
        typename StateSetTypes::Label...
    > StateSetTypeLabelsTuple;

    typedef std::tuple<
        typename StateSetTypes::element_type...
    > StateSetElementTypesTuple;

    using SingletonStateHandler<
        TRepresentation,
        SingletonStateTypes
    >::is_state...;

    using SingletonStateHandler<
        TRepresentation,
        SingletonStateTypes
    >::is_singleton...;

    using SingletonStateHandler<
        TRepresentation,
        SingletonStateTypes
    >::to_representation...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        sizeof...(StateSetIndices)
    >::is_singleton...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        sizeof...(StateSetIndices)
    >::is_state...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        sizeof...(StateSetIndices)
    >::from_representation...;

    using StateSetHandler<
        TRepresentation,
        StateSetTypes,
        StateSetIndices,
        sizeof...(StateSetIndices)
    >::to_representation...;

    static constexpr bool is_singleton(
        TRepresentation representation)
    {
        return (SingletonStateHandler<TRepresentation, SingletonStateTypes>::is_state(
            representation,
            atomic_state_handler_tag<typename SingletonStateTypes::Label>()) || ...);
    }

    template<
        typename TLabel
    > static constexpr bool is(
        TRepresentation representation
    )
    {
        if constexpr (is_singleton(atomic_state_handler_tag<TLabel>()))
        {
            return is_state(
                representation,
                atomic_state_handler_tag<TLabel>()
            );
        }
        else
        {
            return !is_singleton(
                representation
            ) && is_state(
                representation,
                atomic_state_handler_tag<TLabel>()
            );
        }
    }

    template<
        typename TLabel
    > constexpr static auto as(
        TRepresentation representation
    )
    {
        assert(is<TLabel>(representation));

        return from_representation(
            representation,
            atomic_state_handler_tag<TLabel>());
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TAtomicState
> class state;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TRepresentation,
    StateType...TStates
> class basic_atomic_state
    :
BasicAtomicStateHandlers<
    TRepresentation,
    std::tuple<TStates...>
>
{
    template<
        typename TAtomicState
    > friend class state;

    std::atomic<TRepresentation> m_atomicRepresentation;

public:
    typedef state<basic_atomic_state> state_type;
    typedef TRepresentation representation_type;

    // Allow implicit construction from anything that has
    // a to_representation method.
    template<
        typename TElementType
    >
    basic_atomic_state(
        TElementType elementType
    )  noexcept : 
        m_atomicRepresentation(
            basic_atomic_state::BasicAtomicStateHandlers::to_representation(
                elementType))
    {}

    // Allow implicit construction from a state object.
    basic_atomic_state(
        state_type state
    )  noexcept : m_atomicRepresentation(
        state.m_value)
    {}

    void store(
        state_type value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        m_atomicRepresentation.store(
            value.m_value,
            order);
    }

    state_type load(
        std::memory_order order = std::memory_order_seq_cst
    ) const noexcept
    {
        return state_type(m_atomicRepresentation.load(order));
    }

    state_type exchange(
        state_type value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        return state_type
        {
            m_atomicRepresentation.exchange(
                value.m_value,
                order
            )
        };
    }

    bool compare_exchange_strong(
        state_type& expected,
        state_type value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        return m_atomicRepresentation.compare_exchange_strong(
            expected.m_value,
            value.m_value,
            order
        );
    }

    bool compare_exchange_strong(
        state_type& expected,
        state_type value,
        std::memory_order success,
        std::memory_order failure
    ) noexcept
    {
        return m_atomicRepresentation.compare_exchange_strong(
            expected.m_value,
            value.m_value,
            success,
            failure
        );
    }

    bool compare_exchange_weak(
        state_type& expected,
        state_type value,
        std::memory_order order = std::memory_order_seq_cst
    ) noexcept
    {
        return m_atomicRepresentation.compare_exchange_weak(
            expected.m_value,
            value.m_value,
            order
        );
    }

    bool compare_exchange_weak(
        state_type& expected,
        state_type value,
        std::memory_order success,
        std::memory_order failure
    ) noexcept
    {
        return m_atomicRepresentation.compare_exchange_weak(
            expected.m_value,
            value.m_value,
            success,
            failure
        );
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename...TStates
> using atomic_state = basic_atomic_state<void*, TStates...>;

// This represents a concrete generic state.
// It comparable to other states via implicit conversions to this type.
template<
    typename TRepresentation,
    typename...TStates
> class state<
    basic_atomic_state<TRepresentation, TStates...>
>
    :
private BasicAtomicStateHandlers<
    TRepresentation,
    std::tuple<TStates...>
>
{
    // Allow basic_atomic_state access to private members.
    template<
        typename,
        StateType...
    > friend class basic_atomic_state;

    typedef basic_atomic_state<TRepresentation, TStates...> atomic_state;

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
        typename TElementType
    >
    state(
        TElementType elementType
    ) : m_value(
        atomic_state::to_representation(
            elementType))
    {}

    // Allow implicit construction from anything that has
    // a specific to_representation method.
    template<
        typename TLabel,
        typename TElementType
    >
        state(
            TLabel label,
            TElementType elementType
        ) : m_value(
            atomic_state::to_representation(
                elementType,
                atomic_state_handler_tag<TLabel>{}))
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

    template<
        typename TLabel
    > constexpr bool is() const
    {
        return atomic_state::template is<TLabel>(
            m_value);
    }

    template<
        typename TLabel
    > constexpr auto as() const
    {
        return atomic_state::template as<TLabel>(
            m_value);
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename AtomicState
> concept is_atomic_state_type = is_template_instantiation<AtomicState, basic_atomic_state>;

template<
    typename Lambda,
    typename AtomicState
> concept is_compare_exchange_weak_loop_lambda = 
is_atomic_state_type<AtomicState>
&&
    requires(typename AtomicState::state_type state, Lambda lambda)
{
    { lambda(state) } -> std::convertible_to<std::optional<typename AtomicState::state_type>>;
};

PHANTOM_COROUTINES_MODULE_EXPORT
// TNextStateLambda should return either a state_type or an std::optional<state_type>.
template <
    is_atomic_state_type TAtomicState,
    is_compare_exchange_weak_loop_lambda<TAtomicState> TNextStateLambda
>
auto compare_exchange_weak_loop(
    TAtomicState& atomicState,
    TNextStateLambda nextStateLambda,
    std::memory_order loadMemoryOrder = std::memory_order_acquire,
    std::memory_order successMemoryOrder = std::memory_order_acq_rel,
    std::memory_order failureMemoryOrder = std::memory_order_acquire
) noexcept
{
    auto previousState = atomicState.load(
        loadMemoryOrder
    );

    while (true)
    {
        std::optional<typename TAtomicState::state_type> nextState = nextStateLambda(
            previousState
        );

        if (!nextState
            ||
            atomicState.compare_exchange_weak(
                previousState,
                *nextState,
                successMemoryOrder,
                failureMemoryOrder
            ))
        {
            break;
        }
    }

    return previousState;
}

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::SingletonState;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::StateSet;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::StateSetTraits;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_atomic_state;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::atomic_state;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::state;

}
#endif
