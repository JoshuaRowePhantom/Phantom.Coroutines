cmake_minimum_required (VERSION 3.17)

add_library (
    Phantom.Coroutines
    assert_same_thread.ixx
    async_auto_reset_event.ixx
    async_generator.ixx
    async_manual_reset_event.ixx
    async_mutex.ixx
    async_promise.ixx
    async_scope.ixx
    atomic_state.ixx
    consecutive_global_id.ixx
    coroutine.ixx
    early_termination_task.ixx
    error_condition_early_termination.ixx
    fibonacci_heap.ixx
    final_suspend_transfer.ixx
    generator.ixx
    immovable_object.ixx
    inline_scheduler.ixx
    non_copyable.ixx
    promise_traits.ixx
    read_copy_update.ixx
    reusable_consecutive_global_id.ixx
    scheduler.ixx
    scope_guard.ixx
    sequence_barrier.ixx
    shared_task.ixx
    single_consumer_auto_reset_event.ixx
    single_consumer_event.ixx
    single_consumer_manual_reset_event.ixx
    single_consumer_promise.ixx
    static_thread_pool.ixx
    storage_for.ixx
    suspend_result.ixx
    sync_wait.ixx
    task.ixx
    
    thread_pool_scheduler.ixx
    type_traits.ixx
    variant_member.ixx
    variant_result_storage.ixx
    when_ready.ixx
)

target_include_directories(
    Phantom.Coroutines
    INTERFACE
    include)
    