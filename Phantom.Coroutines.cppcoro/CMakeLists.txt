cmake_minimum_required (VERSION 3.30)

add_library (
    Phantom.Coroutines.cppcoro
    INTERFACE
)

target_include_directories(
    Phantom.Coroutines.cppcoro
    INTERFACE
    include)

target_link_libraries(
    Phantom.Coroutines.cppcoro
    INTERFACE
    Phantom.Coroutines)
