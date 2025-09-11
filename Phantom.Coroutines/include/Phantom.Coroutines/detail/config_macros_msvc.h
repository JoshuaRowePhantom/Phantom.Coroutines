#define PHANTOM_COROUTINES_COMPILER_MSVC 1

// Using MSVC
// Bug https ://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
#ifndef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#define PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE 1
#endif

// Bug https://developercommunity.visualstudio.com/t/Incorrect-code-generation-for-symmetric/1659260?q=%22symmetric+transfer%22
#ifndef PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME
#define PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME 1
#endif

// Bug https://developercommunity.visualstudio.com/t/Incorrect-code-generation-for-symmetric/1659260?q=%22symmetric+transfer%22
#ifndef PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME
#define PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME 1
#endif

// Bug https://developercommunity.visualstudio.com/t/MSVC-accepts-lambda-expression-referring/10306965
#ifndef PHANTOM_COROUTINES_NO_REJECT_LAMBDA_WITH_INVALID_MEMBER
#define PHANTOM_COROUTINES_NO_REJECT_LAMBDA_WITH_INVALID_MEMBER 1
#endif

// MSVC captures the result of get_return_object as-is.
#define PHANTOM_COROUTINES_USE_REFERENCE_WRAPPER_RETURN_TYPE_FOR_GET_RETURN_OBJECT 0

// MSVC does present the lambda object as the first reference
// argument to the promise constructor.
#define PHANTOM_COROUTINES_LAMBDA_REFERENCE_IS_FIRST_ARGUMENT_OF_PROMISE_CONSTRUCTOR 1

#define PHANTOM_COROUTINES_MSVC_INSTRINSIC [[msvc::intrinsic]]
#define PHANTOM_COROUTINES_MSVC_FORCEINLINE [[msvc::forceinline]]
#define PHANTOM_COROUTINES_MSVC_SUPPRESS_PACKING_ALIGNMENT_WARNING __pragma(warning(suppress:4324))

#define PHANTOM_COROUTINES_MSVC_PUSH_DISABLE_WARNING(warnings) __pragma(warning(push)) __pragma(warning(disable: warnings))
#define PHANTOM_COROUTINES_MSVC_POP() __pragma(warning(pop))
