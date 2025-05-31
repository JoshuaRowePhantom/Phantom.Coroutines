#include <gtest/gtest.h>
#include <concepts>
#include "Phantom.Coroutines/detail/config_macros.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.friendly_coroutine_traits;
import Phantom.Coroutines.stateful_metaprogramming;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/detail/coroutine.h"
#include "Phantom.Coroutines/detail/friendly_coroutine_traits.h"
#include "Phantom.Coroutines/detail/stateful_metaprogramming.h"
#endif

namespace Phantom::Coroutines
{

struct friendly_coroutine_traits_test
{
    template<typename ...>
    struct test_promise_type {};

    struct test_future_type_1 {};
    struct test_future_type_2 {};
    struct test_future_type_3 {};

    template<typename Result, typename ...>
    struct test_future_coroutine_traits;

    template<
        typename ... Args
    >
    struct test_future_coroutine_traits<
        test_future_type_1,
        Args...
    >
    {
        using promise_type = test_promise_type<test_future_type_1, Args...>;
    };
    
    template<
        typename ... Args
    >
    struct test_future_coroutine_traits<
        test_future_type_3,
        Args...
    >
    {
        using promise_type = test_promise_type<test_future_type_3, Args...>;
    };

    static_assert(add_coroutine_traits<
        test_future_coroutine_traits>);

    struct test_future_type_4
    {
    };

    template<
        typename Future,
        typename ... Args
    >
    struct test_friend_future_coroutine_traits
    {
        using promise_type = test_promise_type<Future, Args...>;
    };

    template<
        typename ... Args
    >
    friend consteval auto friend_coroutine_traits(
        const test_future_type_4& future,
        Args&&... args
    )
    {
        return test_friend_future_coroutine_traits
        <
            test_future_type_4
        >{};
    }

    static_assert(!detail::has_friendly_coroutine_traits<test_future_type_2>);
    static_assert(!detail::has_friendly_coroutine_traits<test_future_type_4>);
};

} // namespace Phantom::Coroutines

namespace std
{

template<
    typename ... Args
>
struct coroutine_traits<
    Phantom::Coroutines::friendly_coroutine_traits_test::test_future_type_2,
    Args...
>
{
    using promise_type = Phantom::Coroutines::friendly_coroutine_traits_test::test_promise_type<
        Phantom::Coroutines::friendly_coroutine_traits_test::test_future_type_2, 
        Args...
    >;
};

}

namespace Phantom::Coroutines
{
static_assert(std::same_as<
    friendly_coroutine_traits_test::test_promise_type<
        friendly_coroutine_traits_test::test_future_type_1
    >,
    std::coroutine_traits<
        friendly_coroutine_traits_test::test_future_type_1
    >::promise_type
>);

static_assert(std::same_as<
    friendly_coroutine_traits_test::test_promise_type<
        friendly_coroutine_traits_test::test_future_type_2
    >,
    std::coroutine_traits<
        friendly_coroutine_traits_test::test_future_type_2
    >::promise_type
>);

static_assert(std::same_as<
    friendly_coroutine_traits_test::test_promise_type<
        friendly_coroutine_traits_test::test_future_type_3
    >,
    std::coroutine_traits<
        friendly_coroutine_traits_test::test_future_type_3
    >::promise_type
>);

static_assert(std::same_as<
    friendly_coroutine_traits_test::test_promise_type<
        friendly_coroutine_traits_test::test_future_type_4
    >,
    std::coroutine_traits<
        friendly_coroutine_traits_test::test_future_type_4
    >::promise_type
>);

}