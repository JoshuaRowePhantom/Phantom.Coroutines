cmake_minimum_required (VERSION 3.17)
project(Phantom.Coroutines)

find_package(GTest REQUIRED)

if (MSVC)
	add_compile_options("/std:c++latest")
	add_compile_options("/Fa")
endif()

add_subdirectory(Phantom.Coroutines)
add_subdirectory(Phantom.Coroutines.Test)
add_subdirectory(Phantom.Coroutines.cppcoro)
add_subdirectory(Phantom.Coroutines.cppcoro.Test)

enable_testing()
