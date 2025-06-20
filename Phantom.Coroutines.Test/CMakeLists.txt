cmake_minimum_required (VERSION 3.30)

set(
    PhantomCoroutinesTestSources
    "aligned_array_test.cpp"
    "async_atomic_test.cpp"
    "async_auto_reset_event_test.cpp"
    "async_generator_test.cpp"
    "async_latch_test.cpp" 
    "async_manual_reset_event_test.cpp"
    "async_mutex_test.cpp"
    "async_promise_test.cpp" 
    "async_reader_writer_lock_test.cpp" 
    "async_scope_test.cpp"
    "async_sequence_barrier_test.cpp"
    "async_sharded_reader_writer_lock_test.cpp"
    "async_test.cpp"
    "async_test.h"
    "atomic_state_test.cpp"
    "awaiter_list_test.cpp" 
    "contextual_promise_test.cpp" 
    "detail/awaiter_wrapper_test.cpp"   
    "detail/awaiters.h"
    "detail/fibonacci_heap_test.cpp"
    "detail/non_copyable_test.cpp"
    "detail/scope_guard_test.cpp"
    "detail/variant_result_storage_test.cpp"
    "direct_initialized_optional_test.cpp"
    "double_wide_atomic_test.cpp" 
    "early_termination_task_test.cpp"
    "generator_test.cpp"
    "inline_scheduler_test.cpp"
    "make_Task_test.cpp" 
    "manual_scheduler.h"
    "nonatomic_shared_ptr_test.cpp"
    "nonatomic_shared_ptr_test.cpp"
    "pmr_task.h" 
    "promise_allocator_test.cpp" 
    "read_copy_update_test.cpp"
    "reusable_consecutive_global_id_test.cpp"
    "reusable_task_test.cpp" 
    "sequence_lock_test.cpp" 
    "sharding_test.cpp"
    "shared_task_test.cpp"
    "suspend_result_test.cpp" 
    "sync_wait_test.cpp"
    "tagged_pointer_test.cpp"
    "task_test.cpp"
    "thread_local_contextual_promise_test.cpp"
    "thread_local_storage_test.cpp"
    "thread_pool_scheduler_test.cpp"
    "type_traits_test.cpp"
)

add_executable(
    Phantom.Coroutines.Test
    ${PhantomCoroutinesTestSources}
)

target_compile_definitions(
    Phantom.Coroutines.Test
    PRIVATE
    PHANTOM_COROUTINES_TESTING_HEADERS
)

target_link_libraries(
    Phantom.Coroutines.Test
    PUBLIC
    Phantom.Coroutines
    GTest::gtest
    GTest::gtest_main
)

if(DISABLE_LINK_MODULES)
    add_library(
        Phantom.Coroutines.Modules.Test
        ${PhantomCoroutinesTestSources}
    )
else()
    add_executable(
        Phantom.Coroutines.Modules.Test
        ${PhantomCoroutinesTestSources}
    )
endif()

target_sources(
    Phantom.Coroutines.Modules.Test
    PUBLIC
    FILE_SET CXX_MODULES
    TYPE CXX_MODULES
    FILES
    "lifetime_tracker.ixx"
    "pmr_task.ixx"
)

target_compile_definitions(
    Phantom.Coroutines.Modules.Test
    PRIVATE
    PHANTOM_COROUTINES_TESTING_MODULES
    PHANTOM_COROUTINES_COMPILING_MODULES
    PHANTOM_COROUTINES_IS_COMPILED_MODULE=0
)

target_link_libraries(
    Phantom.Coroutines.Modules.Test
    PUBLIC
    Phantom.Coroutines
    Phantom.Coroutines.Modules
    GTest::gtest
    GTest::gtest_main
)

set_target_properties(
    Phantom.Coroutines.Modules.Test
    PROPERTIES
    CXX_SCAN_FOR_MODULES true)

if(DISABLE_LINK_MODULES)
    add_library(
        Phantom.Coroutines.SingleModule.Test
        ${PhantomCoroutinesTestSources}
    )
else()
    add_executable(
        Phantom.Coroutines.SingleModule.Test
        ${PhantomCoroutinesTestSources}
    )
endif()

target_sources(
    Phantom.Coroutines.SingleModule.Test
    PUBLIC
    FILE_SET CXX_MODULES
    TYPE CXX_MODULES
    FILES
    "lifetime_tracker.ixx"
    "pmr_task.ixx"
)

target_compile_definitions(
    Phantom.Coroutines.SingleModule.Test
    PRIVATE
    PHANTOM_COROUTINES_TESTING_SINGLE_MODULE
    PHANTOM_COROUTINES_COMPILING_MODULES
    PHANTOM_COROUTINES_IS_COMPILED_MODULE=0
)

target_link_libraries(
    Phantom.Coroutines.SingleModule.Test
    PUBLIC
    Phantom.Coroutines
    Phantom.Coroutines.Modules
    GTest::gtest
    GTest::gtest_main
)

set_target_properties(
    Phantom.Coroutines.SingleModule.Test
    PROPERTIES
    CXX_SCAN_FOR_MODULES true)

enable_testing()

gtest_discover_tests(
    Phantom.Coroutines.Test
    EXTRA_ARGS "--gtest_break_on_failure")

if(NOT DISABLE_LINK_MODULES)
    gtest_discover_tests(
        Phantom.Coroutines.Modules.Test
        EXTRA_ARGS "--gtest_break_on_failure")
    
    gtest_discover_tests(
        Phantom.Coroutines.SingleModule.Test
        EXTRA_ARGS "--gtest_break_on_failure")
endif()

if(DISABLE_COMPILE_MODULES)
    set_target_properties(
        Phantom.Coroutines.Modules.Test 
        PROPERTIES
        EXCLUDE_FROM_ALL TRUE)
    set_target_properties(
        Phantom.Coroutines.SingleModule.Test 
        PROPERTIES
        EXCLUDE_FROM_ALL TRUE)
endif()
