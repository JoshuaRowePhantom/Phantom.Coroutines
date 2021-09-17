cmake_minimum_required (VERSION 3.17)
project(Phantom.Coroutines)

find_package(GTest REQUIRED)

if (MSVC)
	add_compile_options("/std:c++20")
	add_compile_options("/Fa")
endif()

add_subdirectory(Phantom.Coroutines)
add_subdirectory(Phantom.Coroutines.Test)

enable_testing()
