import "gtest.h";
import Phantom.Coroutines.scope_guard;
import <optional>;

namespace Phantom::Coroutines
{

TEST(scope_guard_test, invokes_lambda_on_destruction)
{
	bool invoked = false;
	{
		scope_guard guard{ [&]() { invoked = true; } };
		ASSERT_EQ(false, invoked);
	}
	ASSERT_EQ(true, invoked);
}

}