cmake_minimum_required (VERSION 3.17)
project(Phantom.Coroutines)

find_package(GTest REQUIRED)

if (MSVC)
    add_compile_options("/std:c++latest")
    
    # Bug https://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
    add_compile_options("/DPHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE=1")
    if(CMAKE_SIZEOF_VOID_P EQUAL 8)
        # This is to make Intellisense work.
        add_compile_options("/D_M_AMD64=100")
    endif()
endif()

add_subdirectory(Phantom.Coroutines)
add_subdirectory(Phantom.Coroutines.Test)
add_subdirectory(Phantom.Coroutines.cppcoro)
add_subdirectory(Phantom.Coroutines.cppcoro.Test)

enable_testing()
