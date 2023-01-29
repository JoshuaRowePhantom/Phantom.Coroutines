#pragma once

#ifdef _MSVC_LANG

// Bug https ://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
#ifndef PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE
#define PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE 1
#endif

#endif
