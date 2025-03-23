cmake_minimum_required (VERSION 3.30)

add_library(
    Phantom.Coroutines.Modules
)

target_compile_definitions(
    Phantom.Coroutines.Modules
    PRIVATE
    PHANTOM_COROUTINES_COMPILING_MODULES=1
    PHANTOM_COROUTINES_IS_COMPILED_MODULE=1
)

target_sources(
    Phantom.Coroutines.Modules
    PUBLIC
    FILE_SET CXX_MODULES
    TYPE CXX_MODULES
    FILES
    "aligned_array.ixx"
    "assert_same_thread.ixx"
    "async_auto_reset_event.ixx"
    "async_generator.ixx" 
    "async_latch.ixx" 
    "async_manual_reset_event.ixx"  
    "async_mutex.ixx"
    "async_promise.ixx" 
    "async_reader_writer_lock.ixx" 
    "async_scope.ixx" 
    "async_sequence_barrier.ixx"
    "async_sharded_reader_writer_lock.ixx"
    "atomic_state.ixx"
    "await_all_await_transform.ixx"
    "await_none_await_transform.ixx"
    "awaiter_list.ixx"
    "awaiter_wrapper.ixx"
    "consecutive_global_id.ixx" 
    "consecutive_thread_id.ixx"
    "contextual_promise.ixx"
    "core_task.ixx"
    "coroutine.ixx" 
    "direct_initialized_optional.ixx"
    "double_wide_atomic.ixx"
    "early_termination_task.ixx" 
    "error_condition_early_termination.ixx" 
    "expected_early_termination.ixx" 
    "extensible_promise.ixx"
    "fibonacci_heap.ixx" 
    "final_suspend_transfer.ixx"
    "generator.ixx" 
    "immovable_object.ixx"
    "inline_scheduler.ixx"
    "make_task.ixx"
    "non_copyable.ixx"
    "nonatomic_shared_ptr.ixx"
    "Phantom.Coroutines.ixx" 
    "policies.ixx"
    "promise_allocator.ixx" 
    "read_copy_update.ixx"
    "reusable_consecutive_global_id.ixx"
    "reusable_task.ixx"
    "scheduler.ixx"
    "scope_guard.ixx"
    "sequence_lock.ixx"
    "sharding.ixx"
    "shared_task.ixx"
    "static_thread_pool.ixx"
    "storage_for.ixx"
    "suspend_result.ixx"
    "sync_wait.ixx"
    "tagged_pointer.ixx" 
    "task.ixx"
    "thread_local_context.ixx"
    "thread_local_storage.ixx" 
    "type_traits.ixx"
    "variant_result_storage.ixx" 
     "thread_local_contextual_promise.ixx")

target_link_libraries(
    Phantom.Coroutines.Modules
    PRIVATE
    Phantom.Coroutines
)

set_target_properties(
    Phantom.Coroutines.Modules
    PROPERTIES
    CXX_SCAN_FOR_MODULES true)
