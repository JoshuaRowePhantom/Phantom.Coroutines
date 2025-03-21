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
    "aligned_array.ixx"
    "assert_same_thread.ixx"
    "atomic_state.ixx"
    "consecutive_thread_id.ixx"
    "coroutine.ixx" 
    "extensible_promise.ixx"
    "immovable_object.ixx"
    "non_copyable.ixx"
    "nonatomic_shared_ptr.ixx"
    "Phantom.Coroutines.ixx" 
    "policies.ixx"
    "read_copy_update.ixx"
    "reusable_consecutive_global_id.ixx"
    "scope_guard.ixx"
    "sequence_lock.ixx"
    "thread_local_storage.ixx" 
    "type_traits.ixx"
 "fibonacci_heap.ixx")

target_link_libraries(
    Phantom.Coroutines.Modules
    PRIVATE
    Phantom.Coroutines
)
