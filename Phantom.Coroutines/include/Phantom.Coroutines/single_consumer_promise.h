#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/storage_for.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename TValue
>
class single_consumer_promise
    :
storage_for<TValue>
{
    using storage_for<TValue>::m_storage;

    struct IncompleteState {};
    struct CompleteState {};
    struct WaitingCoroutineState;

    typedef atomic_state<
        SingletonState<IncompleteState>,
        SingletonState<CompleteState>,
        StateSet<WaitingCoroutineState, coroutine_handle<>>
    > atomic_state_type;

    atomic_state_type m_atomicState;
    typedef state<atomic_state_type> state_type;

    TValue* getValue() { return reinterpret_cast<TValue*>(&m_storage); }

public:
    single_consumer_promise()
        :
        m_atomicState(IncompleteState{})
    {}

    template<
        typename TValue
    >
    explicit single_consumer_promise(
        TValue&& value
    )
        :
        m_atomicState(CompleteState{})
    {
        new (&m_storage) TValue(
            std::forward<TValue>(value)...
        );
    }

    ~single_consumer_promise()
    {
        auto state = m_atomicState.load(
            std::memory_order_acquire
        );

        if (state == CompleteState{})
        {
            getValue()->~TValue();
        }

        assert(!state.is<WaitingCoroutineState>());
    }

    template<
        typename ... TArguments
    > single_consumer_promise& emplace(
        TArguments&&... arguments
    )
    {
        new (&m_storage) TValue(
            std::forward<TArguments>(arguments)...
        );

        auto previousState = m_atomicState.exchange(
            CompleteState{},
            std::memory_order_acq_rel
        );

        if (previousState.is<WaitingCoroutineState>())
        {
            previousState.as<WaitingCoroutineState>().resume();
        }

        return *this;
    }

    bool await_ready()
    {
        return m_atomicState.load(std::memory_order_acquire) == CompleteState{};
    }

    bool await_suspend(
        coroutine_handle<> coroutine
    )
    {
        auto nextStateLambda = [&](state_type previousState) -> state_type
        {
            if (previousState == CompleteState{})
            {
                return CompleteState{};
            }
            return coroutine;
        };

        auto previousState = compare_exchange_weak_loop(
            m_atomicState,
            nextStateLambda,
            std::memory_order_relaxed
        );

        assert(!previousState.is<WaitingCoroutineState>());

        return previousState == CompleteState{};
    }

    TValue& await_ready()
    {
        return *getValue();
    }
};

}

using detail::single_consumer_promise;
}
