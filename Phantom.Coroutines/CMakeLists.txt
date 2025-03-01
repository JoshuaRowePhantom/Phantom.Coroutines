cmake_minimum_required (VERSION 3.30)

add_library (
    Phantom.Coroutines
    INTERFACE
)

target_include_directories(
    Phantom.Coroutines
    INTERFACE
    include)
    