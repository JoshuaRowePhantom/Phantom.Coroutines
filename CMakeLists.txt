cmake_minimum_required (VERSION 3.17)
project(Phantom.Coroutines)

find_package(GTest REQUIRED)

if (MSVC)
	add_compile_options("/std:c++latest")
	add_compile_options("/Fa")
	
	# Bug https://developercommunity.visualstudio.com/t/msvc-2022-c-stdfuture-still-requires-default-const/1582239
	add_compile_options("/DPHANTOM_COROUTINES_FUTURE_DOESNT_ACCEPT_NOT_DEFAULT_CONSTRUCTIBLE=1")
endif()

add_subdirectory(Phantom.Coroutines)
add_subdirectory(Phantom.Coroutines.Test)
add_subdirectory(Phantom.Coroutines.cppcoro)
add_subdirectory(Phantom.Coroutines.cppcoro.Test)

enable_testing()
