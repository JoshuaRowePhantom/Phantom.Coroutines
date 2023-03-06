#pragma once

#ifdef _MSVC_LANG

// Bug https ://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
#ifndef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#define PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE 1
#endif

// Bug https://developercommunity.visualstudio.com/t/Incorrect-code-generation-for-symmetric/1659260?q=%22symmetric+transfer%22
#ifndef PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME
#define PHANTOM_COROUTINES_SYMMETRIC_TRANSFER_INCORRECTLY_LIFTED_TO_COROUTINE_FRAME 1
#endif

#endif
