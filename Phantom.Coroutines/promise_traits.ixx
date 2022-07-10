export module Phantom.Coroutines.promise_traits;
import Phantom.Coroutines.coroutine;

namespace Phantom::Coroutines
{

export template<
    typename TPromise
>
struct promise_traits
{
    typedef TPromise promise_type;
    typedef coroutine_handle<TPromise> coroutine_handle_type;

    auto get_coroutine_handle()
    {
        return coroutine_handle_type::from_promise(
            *static_cast<promise_type*>(this)
        );
    }
};
}