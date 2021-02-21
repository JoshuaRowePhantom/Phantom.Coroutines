cmake_minimum_required (VERSION 3.17)

add_library (
    Phantom.Coroutines
    STATIC
    include/Phantom.Coroutines/single_consumer_auto_reset_event.h
    include/Phantom.Coroutines/task.h
    include/Phantom.Coroutines/atomic_State.h
    include/Phantom.Coroutines/detail/coroutine.h
    include/Phantom.Coroutines/detail/promise_traits.h
    include/Phantom.Coroutines/detail/type_traits.h
    src/single_consumer_auto_reset_event.cpp
)

target_include_directories(
    Phantom.Coroutines
    PUBLIC
    include)
    