#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.awaiter_list;
import Phantom.Coroutines.policies;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/awaiter_list.h"
#include "Phantom.Coroutines/policies.h"
#endif

namespace Phantom::Coroutines
{

namespace
{
struct test_awaiter : awaiter_list_entry<multiple_awaiters, test_awaiter>
{
};
}

TEST(awaiter_list_test, reverse_and_prepend_awaiter_list_handles_null_lists)
{
    test_awaiter* destination = nullptr;
    test_awaiter* source = nullptr;

    reverse_and_prepend_awaiter_list(
        source,
        &destination);

    ASSERT_EQ(nullptr, destination);
    ASSERT_EQ(nullptr, source);
}

TEST(awaiter_list_test, reverse_and_prepend_awaiter_list_handles_null_source_list)
{
    test_awaiter awaiter1;

    test_awaiter* destination = &awaiter1;
    test_awaiter* source = nullptr;

    reverse_and_prepend_awaiter_list(
        source,
        &destination);

    ASSERT_EQ(&awaiter1, destination);
    ASSERT_EQ(nullptr, destination->next());
    ASSERT_EQ(nullptr, source);
}

TEST(awaiter_list_test, reverse_and_prepend_awaiter_list_handles_null_destination_list)
{
    test_awaiter awaiter1;

    test_awaiter* destination = nullptr;
    test_awaiter* source = &awaiter1;

    reverse_and_prepend_awaiter_list(
        source,
        &destination);

    ASSERT_EQ(&awaiter1, destination);
    ASSERT_EQ(&awaiter1, source);
    ASSERT_EQ(nullptr, source->next());
}

TEST(awaiter_list_test, reverse_and_prepend_awaiter_list_does_indeed_reverse_source_and_prepend_to_destination)
{
    test_awaiter awaiter1;
    test_awaiter awaiter2;
    test_awaiter awaiter3;
    test_awaiter awaiter4;

    test_awaiter* destination = &awaiter1;
    awaiter1.set_next(&awaiter2);
    test_awaiter* source = &awaiter3;
    awaiter3.set_next(&awaiter4);

    reverse_and_prepend_awaiter_list(
        source,
        &destination);

    ASSERT_EQ(&awaiter4, destination);
    ASSERT_EQ(&awaiter3, awaiter4.next());
    ASSERT_EQ(&awaiter1, awaiter3.next());
    ASSERT_EQ(&awaiter2, awaiter1.next());
    ASSERT_EQ(nullptr, awaiter2.next());
    ASSERT_EQ(&awaiter3, source);
}

}
