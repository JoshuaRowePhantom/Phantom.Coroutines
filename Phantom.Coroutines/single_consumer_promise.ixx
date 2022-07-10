//export module Phantom.Coroutines.single_consumer_promise;
//
//import Phantom.Coroutines.atomic_state;
//import Phantom.Coroutines.coroutine;
//import Phantom.Coroutines.storage_for;
//
//namespace Phantom::Coroutines
//{
//
//export template<
//    typename TValue
//>
//class single_consumer_promise
//    :
//private storage_for<TValue>
//{
//    using storage_for<TValue>::m_storage;
//
//    struct IncompleteState {};
//    struct CompleteState {};
//    struct WaitingCoroutineState;
//
//    typedef atomic_state<
//        SingletonState<IncompleteState>,
//        SingletonState<CompleteState>,
//        StateSet<WaitingCoroutineState, coroutine_handle<>>
//    > atomic_state_type;
//
//    atomic_state_type m_atomicState;
//    typedef state<atomic_state_type> state_type;
//
//    class awaiter
//    {
//        template<
//            typename TValue
//        > friend class single_consumer_promise;
//
//        single_consumer_promise& m_promise;
//
//        awaiter(
//            single_consumer_promise& promise
//        ) : 
//            m_promise { promise }
//        {}
//
//    public:
//        bool await_ready()
//        {
//            return m_promise.m_atomicState.load(std::memory_order_acquire) == CompleteState{};
//        }
//
//        bool await_suspend(
//            coroutine_handle<> coroutine
//        )
//        {
//            auto nextStateLambda = [&](state_type previousState) -> state_type
//            {
//                if (previousState == CompleteState{})
//                {
//                    return CompleteState{};
//                }
//                return coroutine;
//            };
//
//            auto previousState = compare_exchange_weak_loop(
//                m_promise.m_atomicState,
//                nextStateLambda,
//                std::memory_order_relaxed
//            );
//
//            assert(!previousState.is<WaitingCoroutineState>());
//
//            return previousState != CompleteState{};
//        }
//
//        TValue& await_resume()
//        {
//            assert(m_promise.m_atomicState.load(std::memory_order_relaxed) == CompleteState{});
//            return m_promise.as<TValue>();
//        }
//    };
//
//public:
//    single_consumer_promise()
//        :
//        m_atomicState(IncompleteState{})
//    {}
//
//    single_consumer_promise(
//        const single_consumer_promise&
//    ) = delete;
//
//    single_consumer_promise(
//        single_consumer_promise&&
//    ) = delete;
//
//    template<
//        typename ... TConstructorArguments
//    >
//    explicit single_consumer_promise(
//        TConstructorArguments&&... args
//    )
//        :
//        m_atomicState(CompleteState{})
//    {
//        single_consumer_promise::storage_for::template emplace<TValue>(
//            std::forward<TConstructorArguments>(args)...
//        );
//    }
//
//    ~single_consumer_promise()
//    {
//        auto state = m_atomicState.load(
//            std::memory_order_acquire
//        );
//
//        if (state == CompleteState{})
//        {
//            single_consumer_promise::storage_for::template destroy<TValue>();
//        }
//
//        assert(!state.is<WaitingCoroutineState>());
//    }
//
//    template<
//        typename ... TArguments
//    > TValue& emplace(
//        TArguments&&... arguments
//    )
//    {
//        single_consumer_promise::storage_for::template emplace<TValue>(
//            std::forward<TArguments>(arguments)...);
//
//        auto previousState = m_atomicState.exchange(
//            CompleteState{},
//            std::memory_order_acq_rel
//        );
//
//        if (previousState.is<WaitingCoroutineState>())
//        {
//            previousState.as<WaitingCoroutineState>().resume();
//        }
//
//        return this->as<TValue>();
//    }
//
//    awaiter operator co_await() { return { *this }; }
//};
//
//}
//
