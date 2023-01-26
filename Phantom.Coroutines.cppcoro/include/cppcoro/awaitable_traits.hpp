#include "Phantom.Coroutines/type_traits.h"

namespace cppcoro
{

template<
    typename Awaitable
> struct awaitable_traits
{};

template<
    typename Awaitable
>
requires ::Phantom::Coroutines::is_awaitable<Awaitable>
struct awaitable_traits<
    Awaitable
>
{
    using awaiter_t = decltype(::Phantom::Coroutines::get_awaiter(std::declval<Awaitable>()));
    using await_result_t = decltype(std::declval<awaiter_t>().await_resume());
};

}