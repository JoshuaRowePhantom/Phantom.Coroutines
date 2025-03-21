cmake_minimum_required (VERSION 3.30)
project(Phantom.Coroutines)

find_package(GTest REQUIRED)

set(CMAKE_COMPILE_WARNING_AS_ERROR ON)
set(CMAKE_CXX_STANDARD 23)
set(CXX_SCAN_FOR_MODULES true)
add_compile_options($<$<CXX_COMPILER_ID:MSVC>:/W4>)

if (MSVC)
    # Bug https://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
    add_compile_definitions(PHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE=1)
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        # This is to make Intellisense work.
        add_compile_definitions(_M_AMD64=100)
    endif()

    string(REPLACE "/Ob1" "/Ob3" CMAKE_CXX_FLAGS_RELWITHDEBINFO ${CMAKE_CXX_FLAGS_RELWITHDEBINFO})
endif()

add_subdirectory(Phantom.Coroutines)
add_subdirectory(Phantom.Coroutines.Modules)
add_subdirectory(Phantom.Coroutines.Test)
add_subdirectory(Phantom.Coroutines.cppcoro)
add_subdirectory(Phantom.Coroutines.cppcoro.Test)

enable_testing()
