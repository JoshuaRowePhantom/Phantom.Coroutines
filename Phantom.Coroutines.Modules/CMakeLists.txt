cmake_minimum_required (VERSION 3.30)

add_library(
    Phantom.Coroutines.Modules
)

target_compile_definitions(
    Phantom.Coroutines.Modules
    PRIVATE
    PHANTOM_COROUTINES_COMPILING_MODULES
)

target_sources(
    Phantom.Coroutines.Modules
    PUBLIC
    FILE_SET CXX_MODULES
    TYPE CXX_MODULES
    FILES
    "assert_same_thread.ixx"
    "atomic_state.ixx"
    "consecutive_thread_id.ixx"
    "coroutine.ixx" 
    "immovable_object.ixx"
    "non_copyable.ixx"
    "nonatomic_shared_ptr.ixx"
    "read_copy_update.ixx"
    "reusable_consecutive_global_id.ixx"
    "scope_guard.ixx"
    "thread_local_storage.ixx" 
    "type_traits.ixx"
)

target_link_libraries(
    Phantom.Coroutines.Modules
    PRIVATE
    Phantom.Coroutines
)
