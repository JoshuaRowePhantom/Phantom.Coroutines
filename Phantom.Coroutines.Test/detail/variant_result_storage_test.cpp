#include "gtest/gtest.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
import Phantom.Coroutines.Test.lifetime_tracker;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.Test.lifetime_tracker;
import Phantom.Coroutines.type_traits;
import Phantom.Coroutines.variant_result_storage;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/type_traits.h"
#include "Phantom.Coroutines/detail/variant_result_storage.h"
#include "../lifetime_tracker.h"
#endif

namespace Phantom::Coroutines::detail
{

namespace
{
template<
    typename Value
>
struct test_variant_storage
    :
    variant_return_result<Value>,
    variant_result_storage<Value>
{
    using result_variant_member_type = typename variant_result_storage<Value>::result_variant_member_type;
    using variant_type = std::variant<
        std::monostate,
        result_variant_member_type
    >;

    variant_type m_result;

    void return_variant_result(
        result_variant_member_type&& value
    )
    {
        m_result.template emplace<1>(std::forward<decltype(value)>(value));
    }

    decltype(auto) await_resume(
        this auto&& self
    )
    {
        return variant_result_storage<Value>::template resume_variant_result<1>(
            detail::forward_like<decltype(self)>(self.m_result));
    }
};
}

TEST(variant_result_storage_test, can_return_and_resume_void)
{
    test_variant_storage<void> storage;
    storage.return_void();
    static_assert(std::same_as<void, decltype(storage.await_resume())>);
    storage.await_resume();
}

TEST(variant_result_storage_test, resume_variant_result_returns_value_type_by_lvalue_reference_as_lvalue_reference)
{
    lifetime_statistics statistics;
    test_variant_storage<lifetime_tracker> storage;
    storage.return_variant_result(statistics.tracker());
    decltype(auto) result = storage.await_resume();
    static_assert(std::same_as<lifetime_tracker&, decltype(result)>);
    EXPECT_EQ(&result, &std::get<1>(storage.m_result));
    EXPECT_EQ(result, statistics);
}

TEST(variant_result_storage_test, resume_variant_result_returns_value_type_by_rvalue_reference_as_rvalue_reference)
{
    lifetime_statistics statistics;
    test_variant_storage<lifetime_tracker> storage;
    storage.return_variant_result(statistics.tracker());
    decltype(auto) result = std::move(storage).await_resume();
    static_assert(std::same_as<lifetime_tracker&&, decltype(result)>);
    EXPECT_EQ(&result, &std::get<1>(storage.m_result));
    EXPECT_EQ(result, statistics);
}

TEST(variant_result_storage_test, resume_variant_result_returns_lvalue_reference_type_by_lvalue_reference_as_lvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker tracker = statistics.tracker();
    test_variant_storage<lifetime_tracker&> storage;
    storage.return_variant_result(tracker);
    decltype(auto) result = storage.await_resume();
    static_assert(std::same_as<lifetime_tracker&, decltype(result)>);
    EXPECT_EQ(&result, &tracker);
    EXPECT_EQ(result, statistics);
}

TEST(variant_result_storage_test, resume_variant_result_returns_lvalue_reference_type_by_rvalue_reference_as_lvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker tracker = statistics.tracker();
    test_variant_storage<lifetime_tracker&> storage;
    storage.return_variant_result(tracker);
    decltype(auto) result = std::move(storage).await_resume();
    static_assert(std::same_as<lifetime_tracker&, decltype(result)>);
    EXPECT_EQ(&result, &tracker);
    EXPECT_EQ(result, statistics);
}

TEST(variant_result_storage_test, resume_variant_result_returns_rvalue_reference_type_by_lvalue_reference_as_rvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker tracker = statistics.tracker();
    test_variant_storage<lifetime_tracker&&> storage;
    storage.return_variant_result(tracker);
    decltype(auto) result = storage.await_resume();
    static_assert(std::same_as<lifetime_tracker&&, decltype(result)>);
    EXPECT_EQ(&result, &tracker);
    EXPECT_EQ(result, statistics);
}

TEST(variant_result_storage_test, resume_variant_result_returns_rvalue_reference_type_by_rvalue_reference_as_rvalue_reference)
{
    lifetime_statistics statistics;
    lifetime_tracker tracker = statistics.tracker();
    test_variant_storage<lifetime_tracker&&> storage;
    storage.return_variant_result(tracker);
    decltype(auto) result = std::move(storage).await_resume();
    static_assert(std::same_as<lifetime_tracker&&, decltype(result)>);
    EXPECT_EQ(&result, &tracker);
    EXPECT_EQ(result, statistics);
}

}
