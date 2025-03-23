#ifndef PHANTOM_COROUTINES_INCLUDE_CONFIG_H
#define PHANTOM_COROUTINES_INCLUDE_CONFIG_H

#ifdef _MSVC_LANG

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

#if defined(__clang__)
#define PHANTOM_COROUTINES_MSVC_INSTRINSIC
#define PHANTOM_COROUTINES_MSVC_FORCEINLINE
#else
#define PHANTOM_COROUTINES_MSVC_INSTRINSIC [[msvc::intrinsic]]
#define PHANTOM_COROUTINES_MSVC_FORCEINLINE [[msvc::forceinline]]
#endif


#else
#define PHANTOM_COROUTINES_MSVC_INSTRINSIC
#define PHANTOM_COROUTINES_MSVC_FORCEINLINE
#endif // _MSVC_LANG

#if !NDEBUG
#ifndef PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING
#define PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING 1
#endif
#endif

#ifdef PHANTOM_COROUTINES_COMPILING_MODULES
#define PHANTOM_COROUTINES_MODULE_EXPORT export
#else
#define PHANTOM_COROUTINES_MODULE_EXPORT
#endif

#ifndef PHANTOM_COROUTINES_IS_COMPILED_MODULE
#define PHANTOM_COROUTINES_IS_COMPILED_MODULE 0
#endif

#ifndef PHANTOM_COROUTINES_ASSERT_IS_MODULE 
#if defined(PHANTOM_COROUTINES_TESTING_SINGLE_MODULE)
#define PHANTOM_COROUTINES_ASSERT_IS_MODULE static_assert(PHANTOM_COROUTINES_IS_COMPILED_MODULE)
#elif defined(PHANTOM_COROUTINES_TESTING_MODULES)
#define PHANTOM_COROUTINES_ASSERT_IS_MODULE static_assert(PHANTOM_COROUTINES_IS_COMPILED_MODULE)
#else
#define PHANTOM_COROUTINES_ASSERT_IS_MODULE static_assert(true)
#endif
#endif

#define PHANTOM_COROUTINES_IS_CONFIGURED 1

#endif
