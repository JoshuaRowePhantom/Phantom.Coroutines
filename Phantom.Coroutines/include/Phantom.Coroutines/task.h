#pragma once

#include "detail/coroutine.h"
#include "detail/promise_traits.h"
#include <variant>

namespace Phantom::Coroutines
{
//
//template<
//    typename TPromise,
//    typename TFuture
//>
//class task_promise_base
//    :
//    protected promise_traits<TPromise>
//{
//public:
//    auto initial_suspend()
//    {
//        return suspend_always;
//    }
//
//    auto final_suspend()
//    {
//        return suspend_always;
//    }
//
//    auto get_return_object()
//    {
//        return TFuture(
//            promise_traits::get_coroutine_handle()
//        );
//    }
//};
//
//template<
//    typename TPromise,
//    typename TFuture
//>
//class task_promise
//    :
//    public TPromise
//{
//    using TPromise::TPromise;
//};
//
//template<
//    typename TResult = void,
//    typename TPromise = task_promise<TResult>
//>
//class [[nodiscard]] task
//    :
//    protected promise_traits<TPromise>
//{
//public:
//    typedef TPromise promise_type;
//    typedef coroutine_handle<promise_type> coroutine_handle_type;
//    typedef TResult result_type;
//
//private:
//    coroutine_handle_type m_coroutineHandle;
//
//public:
//    task(
//        coroutine_handle_type coroutineHandle = coroutine_handle_type()
//    ) : m_coroutineHandle(
//        coroutineHandle)
//    {}
//};

}