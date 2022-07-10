//import Phantom.Coroutines.type_traits;
//
//namespace Phantom::Coroutines
//{
//namespace detail
//{
//
//template<
//    is_awaitable TAwaitable
//>
//class when_ready_awaitable;
//
//template<
//    is_awaitable TAwaitable
//>
//class when_ready_promise
//{
//public:
//    template<
//        typename TAwaitable
//    > when_ready_awaitable(
//        TAwaitable&& awaitable
//    ) :
//        m_awaitable
//    {
//        std::forward(
//            awaitable)
//    }
//    {}
//
//    never_suspend initial_suspend() { return never_suspend{}; }
//    never_suspend final_suspend() { return final_suspend{}; }
//
//    when_ready_awaitable<TAwaitable> get_return_object()
//    {
//        return when_ready_awaitable{ *this };
//    }
//};
//
//template<
//    is_awaitable TAwaitable
//>
//class when_ready_awaitable
//{
//    TAwaitable m_awaitable;
//
//public:
//    typedef when_ready_promise<TAwaitable> promise_type;
//
//};
//
//template<
//    is_awaitable TAwaitable
//> when_ready_awaitable<TAwaitable>
//when_ready(
//    TAwaitable&& awaitable
//)
//{
//    co_await awaitable;
//}
//
//}
//
//using detail::when_ready;
//}