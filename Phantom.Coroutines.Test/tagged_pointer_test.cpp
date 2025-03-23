#include "async_test.h"
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
import Phantom.Coroutines;
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
import Phantom.Coroutines.tagged_pointer;
#elif defined(PHANTOM_COROUTINES_TESTING_HEADERS)
#include "Phantom.Coroutines/tagged_pointer.h"
#endif

namespace Phantom::Coroutines
{
namespace
{

enum TaggedPointerTag
{
    Zero = 0,
    Seven = 7,
};

// Disable warning that structure padded due to alignment specifier
#pragma warning(push)
#pragma warning(disable:4324)
struct alignas(8) TaggedPointerStruct
{
};
#pragma warning(pop)

}

TEST(tagged_pointer_test, can_initialize_and_retrieve_value_and_tag)
{
    TaggedPointerStruct value;
    tagged_pointer<TaggedPointerStruct, 3, TaggedPointerTag> pointer{ &value, Seven };
    ASSERT_EQ(&value, pointer.value());
    ASSERT_EQ(&value, pointer.operator ->());
    ASSERT_EQ(Seven, pointer.tag());
}


TEST(tagged_pointer_test, can_compare)
{
    TaggedPointerStruct value1;
    TaggedPointerStruct value2;
    tagged_pointer<TaggedPointerStruct, 3, TaggedPointerTag> pointer1{ &value1, Zero };
    tagged_pointer<TaggedPointerStruct, 3, TaggedPointerTag> pointer2{ &value1, Seven };
    tagged_pointer<TaggedPointerStruct, 3, TaggedPointerTag> pointer3{ &value2, Seven };

    ASSERT_TRUE(pointer1 == pointer1);
    ASSERT_FALSE(pointer1 == pointer2);
    ASSERT_FALSE(pointer1 == pointer3);

    ASSERT_FALSE(pointer2 == pointer1);
    ASSERT_TRUE(pointer2 == pointer2);
    ASSERT_FALSE(pointer2 == pointer3);

    ASSERT_FALSE(pointer3 == pointer1);
    ASSERT_FALSE(pointer3 == pointer2);
    ASSERT_TRUE(pointer3 == pointer3);

    ASSERT_FALSE(pointer1 != pointer1);
    ASSERT_TRUE(pointer1 != pointer2);
    ASSERT_TRUE(pointer1 != pointer3);

    ASSERT_TRUE(pointer2 != pointer1);
    ASSERT_FALSE(pointer2 != pointer2);
    ASSERT_TRUE(pointer2 != pointer3);

    ASSERT_TRUE(pointer3 != pointer1);
    ASSERT_TRUE(pointer3 != pointer2);
    ASSERT_FALSE(pointer3 != pointer3);
}
}