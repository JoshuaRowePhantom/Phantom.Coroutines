#pragma once
#include <optional>
#include <type_traits>

namespace Phantom::Coroutines::detail
{
//
//template<
//    typename T = void
//> class State;
//
//template<>
//class State<void>
//{
//    friend class StateHolderBase;
//    void* m_value;
//
//    constexpr State(
//        void* value
//    ) : m_value(value)
//    {}
//
//public:
//    template<
//        typename T
//    > constexpr bool operator==(
//        const State<T> other
//        )
//    {
//        return m_value == other.m_value
//    };
//
//    template<
//        typename T
//    > constexpr bool operator!=(
//        const State<T> other
//        )
//    {
//        return m_value != other.m_value
//    };
//};
//
//static_assert(std::is_trivially_copyable_v<State<>>);
//
//template<
//    typename T
//> class State
//    :
//    public State<>
//{
//    static const State g_value;
//public:
//    State()
//        : State<>(&g_value)
//    {
//    }
//
//    static_assert(std::is_trivially_copyable_v<State<T>>);
//};
//
//template<
//    typename T
//> class State<coroutine_handle<T>>
//    :
//    public State<>
//{
//public:
//    typedef coroutine_handle<T> coroutine_handle_type;
//
//    State(
//        coroutine_handle_type handle
//    ) : State<>(handle.address())
//    {}
//
//    operator coroutine_handle_type() const
//    {
//        return coroutine_handle_type::from_address();
//    }
//
//    operator coroutine_handle<>() const
//    {
//        return coroutine_handle<>::from_address();
//    }
//};
//
//class StateHolderBase
//{
//};
//
//template<
//    typename TOtherState,
//    typename... TAdditionalStates
//>
//class StateHolder
//    :
//    public StateHolderBase
//{
//    template<
//        typename...
//    > struct as_otherstate_impl_args{};
//
//    struct as_otherstate_tag{};
//
//    template<
//        typename StateToCheck
//        typename... AdditionalStatesToCheck
//    > std::optional<State<TOtherState>> as_otherstate_impl(
//        as_otherstate_impl_args<StateToCheck, AdditionalStatesToCheck...>)
//    {
//    }
//
//public:
//    template<
//        typename TState = void
//    > class State;
//
//    template<>
//    class State<void>
//    {
//        friend class StateHolderBase;
//        void* m_value;
//
//        constexpr State(
//            void* value
//        ) : m_value(value)
//        {}
//
//    public:
//        template<
//            typename T
//        > constexpr bool operator==(
//            const State<T> other
//            )
//        {
//            return m_value == other.m_value
//        };
//
//        template<
//            typename T
//        > constexpr bool operator!=(
//            const State<T> other
//            )
//        {
//            return m_value != other.m_value
//        };
//
//        static_assert(std::is_trivially_copyable_v<State<T>>);
//    };
//
//    template<
//        typename T
//    > class State
//        :
//        public State<>
//    {
//        friend class StateHolderBase;
//        static const State g_value;
//
//    public:
//        State()
//            : State<>(&g_value)
//        {
//        }
//
//        static_assert(std::is_trivially_copyable_v<State<T>>);
//    };
//
//    template<
//        typename T
//    > static std::optional<State<TOtherState>> as(
//        std::enable_if_t<
//            std::is_same_v<TOtherState, T>,
//            as_otherstate_tag
//        > = as_otherstate_tag())
//    {
//        return as_otherstate_impl(
//            as_otherstate_impl_args<TAdditionalStates...>());
//    }
//
//    State<> load(
//        const std::memory_order order = std::memory_order_seq_cst
//    ) const noexcept
//    {
//        return State<>(
//            m_value.load(order)
//            );
//    }
//
//    void store(
//        State<> state,
//        const std::memory_order order = std::memory_order_seq_cst
//    ) noexcept
//    {
//        m_value.store(
//            state.m_value,
//            order
//        );
//    }
//
//    State<> exchange(
//        State<> state,
//        const std::memory_order order = std::memory_order_seq_cst
//    )
//    {
//        return m_value.exchange(
//            state.m_value,
//            order
//        );
//    }
//
//    bool compare_exchange_strong(
//        State<>& comparand,
//        State<> value,
//        const std::memory_order order
//    )
//    {
//        return m_value.compare_exchange_strong(
//            comparand.m_value,
//            value.m_value,
//            order
//        );
//    }
//
//    bool compare_exchange_strong(
//        State<>& comparand,
//        State<> value,
//        const std::memory_order successOrder,
//        const std::memory_order failOrder
//    )
//    {
//        return m_value.compare_exchange_strong(
//            comparand.m_value,
//            value.m_value,
//            successOrder,
//            failOrder
//        );
//    }
//
//    bool compare_exchange_weak(
//        State<>& comparand,
//        State<> value,
//        const std::memory_order order
//    )
//    {
//        return m_value.compare_exchange_strong(
//            comparand.m_value,
//            value.m_value,
//            order
//        );
//    }
//
//    bool compare_exchange_weak(
//        State<>& comparand,
//        State<> value,
//        const std::memory_order successOrder,
//        const std::memory_order failOrder
//    )
//    {
//        return m_value.compare_exchange_strong(
//            comparand.m_value,
//            value.m_value,
//            successOrder,
//            failOrder
//        );
//    }
//
//private:
//    std::atomic<State<>> m_value;
//};

}