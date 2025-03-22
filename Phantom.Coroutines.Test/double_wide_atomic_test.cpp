#include "async_test.h"
#ifdef PHANTOM_COROUTINES_TESTING_MODULES
import Phantom.Coroutines.double_wide_atomic;
#else
#include "Phantom.Coroutines/double_wide_atomic.h"
#endif

namespace Phantom::Coroutines
{
namespace
{
struct TestDoubleWide
{
    std::int64_t value1 = 5;
    std::int64_t value2 = 6;
    
    bool friend operator==(
        const TestDoubleWide&,
        const TestDoubleWide&
        ) = default;
};
}

TEST(double_wide_atomic_test, Can_load_and_store)
{
    std::atomic<double_wide_value<TestDoubleWide>> atomic;
    EXPECT_EQ(TestDoubleWide{}, atomic.load());
    atomic.store({ 1, 2  });
    EXPECT_EQ(atomic.load(), (TestDoubleWide { 1, 2 } ));
}

TEST(double_wide_atomic_test, Can_compare_exchange)
{
    std::atomic<double_wide_value<TestDoubleWide>> atomic = { { 5, 6 } };
    double_wide_value<TestDoubleWide> expected = { { 1, 2 } };

    EXPECT_FALSE(atomic.compare_exchange_weak(
        expected,
        { { 3, 4 } }
    ));
    EXPECT_NE(expected, (TestDoubleWide { 3, 4 }));
    EXPECT_EQ(expected, (TestDoubleWide { 5, 6 }));
    EXPECT_EQ(atomic.load(), (TestDoubleWide{ 5, 6 }));

    EXPECT_TRUE(atomic.compare_exchange_weak(
        expected,
        { { 3, 4 } }
    ));

    EXPECT_NE(expected, (TestDoubleWide{ 3, 4 }));
    EXPECT_EQ(expected, (TestDoubleWide{ 5, 6 }));
    EXPECT_EQ(atomic.load(), (TestDoubleWide{ 3, 4 }));
}
}