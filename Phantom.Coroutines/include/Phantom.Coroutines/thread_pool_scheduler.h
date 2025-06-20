#ifndef PHANTOM_COROUTINES_INCLUDE_THREAD_POOL_SCHEDULER_H
#define PHANTOM_COROUTINES_INCLUDE_THREAD_POOL_SCHEDULER_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <assert.h>
#include <algorithm>
#include <atomic>
#include <bit>
#include <memory>
#include <mutex>
#include <new>
#include <shared_mutex>
#include <stop_token>
#include <thread>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include "detail/config.h"
#include "detail/coroutine.h"
#include "policies.h"
#include "read_copy_update.h"
#include "scheduler.h"
#include "task.h"
#include "type_traits.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_continuation Continuation
>
class basic_thread_pool_scheduler;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Policy
> concept is_thread_pool_scheduler_policy
=
is_continuation_type_policy<Policy>;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    is_thread_pool_scheduler_policy ... Policy
> using thread_pool_scheduler = basic_thread_pool_scheduler<
    select_continuation_type<Policy..., default_continuation_type>
>;

// The basic_thread_pool_scheduler implements the algorithms in ThreadPool.tla
// and ThreadPool_Wakeup.tla.
template<
    is_continuation Continuation
>
class basic_thread_pool_scheduler
{
    // Disable warning that structure padded due to alignment specifier
    PHANTOM_COROUTINES_MSVC_SUPPRESS_PACKING_ALIGNMENT_WARNING
    class thread_state
    {
        class queue
        {
            std::vector<Continuation> m_continuations;
            size_t m_mask;

            void resize(
                size_t size
            )
            {
                m_continuations.resize(
                    std::bit_ceil(size)
                );
                m_mask = m_continuations.size() - 1;
            }

        public:
            queue(
                size_t size = 16
            )
            {
                resize(size);
            }

            size_t size()
            {
                return m_continuations.size();
            }

            Continuation& operator[](size_t index)
            {
                return m_continuations[index & m_mask];
            }
            
            queue grow(
                size_t requiredSize,
                size_t currentStealingTail,
                size_t currentHead
            )
            {
                queue result(requiredSize);
                for (auto index = currentStealingTail; index != currentHead; index++)
                {
                    result[index] = (*this)[index];
                }
                return result;
            }
        };

        // Start with variables that are read-only or have very little contention.
        std::atomic<size_t> m_head;
        // The maximum value that m_head may contain without recalcuating 
        // both this value and possibly regrowing the queue.
        size_t m_reservedHead = 0;
        basic_thread_pool_scheduler& m_scheduler;

        // This stores the state of whether the thread is intending
        // to sleep. While sleeping, the thread waits on this variable.
        enum class ProcessingState
        {
            // The thread is inside a call to process_items,
            // and hasn't been stopped.
            Processing,
            // The thread is sleeping.
            Sleeping,
            // The thread has been requested to stop while it is sleeping.
            Sleeping_StopRequested,
            // The thread has been requested to stop while it is processing.
            Processing_StopRequested,
            // The thread has stopped processing, or hasn't started.
            Stopped
        };
        std::atomic<ProcessingState> m_processingState = ProcessingState::Stopped;

        read_copy_update_section<queue> m_queueReadCopyUpdateSection;

        // Align the tail, m_outstandingStealOperations, and m_mutex into a new cache line.
        alignas(std::hardware_destructive_interference_size)
            std::atomic<size_t> m_tail;
        
        // The lowest value that might be in the process of being stolen from.
        // This value can be set to m_tail any time that m_outstandingStealOperations
        // becomes zero.
        std::atomic<size_t> m_stealingTail;

        // The number of outstanding steal operations going on.
        // When this reaches zero, the value of m_reservedTail can be
        // raised.
        alignas(std::hardware_destructive_interference_size)
            std::atomic<size_t> m_outstandingStealOperations = 0;

        // The lock required for stealing and conflict resolution between
        // stealing and enqueuing.
        // m_mutex protects:
        //  m_tail
        //  m_stealingTail
        //  m_outstandingStealOperations
        std::mutex m_mutex;

        void reserve_queue_space(
            size_t newHead,
            read_copy_update_section<queue>::update_operation& queueOperation
        )
        {
            if (m_reservedHead < newHead)
            {
                recalculate_reserved_size_and_grow_queue_if_necessary(
                    newHead,
                    queueOperation
                );
            }
        }

        void recalculate_reserved_size_and_grow_queue_if_necessary(
            size_t newHead,
            read_copy_update_section<queue>::update_operation& queueOperation
        )
        {
            auto reserve_tail = get_tail_to_reserve_from();
            // We reserve an extra one for the temporary location that is
            // used when acquiring a local item.
            auto requiredSize = newHead - reserve_tail + 1;

            if (queueOperation.value().size() < requiredSize)
            {
                queueOperation.emplace(
                    queueOperation.value().grow(
                        requiredSize,
                        reserve_tail,
                        m_head.load(std::memory_order_relaxed)
                    )
                );
                queueOperation.exchange();
            }

            m_reservedHead = reserve_tail - 1 + queueOperation->size();
        }

    public:
        thread_state(
            basic_thread_pool_scheduler& scheduler
        ) : m_scheduler{ scheduler }
        {}

        void enqueue(
            Continuation continuation
        )
        {
            auto queueOperation = m_queueReadCopyUpdateSection.update();

            // Only this thread is allowed to modify m_head, so we can
            // load using relaxed.
            auto head = m_head.load(std::memory_order_relaxed);
            auto newHead = head + 1;

            reserve_queue_space(
                newHead,
                queueOperation);

            queueOperation.value()[head] = continuation;

            // Other threads need to see the value we wrote into the queue,
            // and also m_sleepingThreadCount synchronizes on m_head.
            m_head.store(newHead, std::memory_order_seq_cst);
        }

        [[nodiscard]] bool try_wake()
        {
            auto previousProcessingState = m_processingState.load(std::memory_order_acquire);
            ProcessingState nextProcessingState;

            do
            {
                nextProcessingState = ProcessingState::Processing;
                if (previousProcessingState == ProcessingState::Stopped)
                {
                    nextProcessingState = ProcessingState::Stopped;
                }
                if (previousProcessingState == ProcessingState::Sleeping_StopRequested)
                {
                    nextProcessingState = ProcessingState::Processing_StopRequested;
                }
                if (previousProcessingState == ProcessingState::Processing_StopRequested)
                {
                    nextProcessingState = ProcessingState::Processing_StopRequested;
                }
            } while (!m_processingState.compare_exchange_strong(
                previousProcessingState,
                nextProcessingState,
                std::memory_order_seq_cst
            ));
            
            bool doWakeThread = previousProcessingState == ProcessingState::Sleeping
                || previousProcessingState == ProcessingState::Sleeping_StopRequested;

            if (doWakeThread)
            {
                m_processingState.notify_all();
            }

            return doWakeThread;
        }

        Continuation acquire_local_item()
        {
            auto head = m_head.load(std::memory_order_relaxed);
            // Special case, since head is unsigned
            if (head == 0) { return Continuation{}; }
            auto newHead = head - 1;
            m_head.store(newHead, std::memory_order_seq_cst);

            auto tail = m_tail.load(std::memory_order_seq_cst);
            if (tail > newHead)
            {
                std::scoped_lock lock{ m_mutex };
                tail = m_tail.load(std::memory_order_seq_cst);
                if (tail > newHead)
                {
                    m_head.store(head, std::memory_order_seq_cst);
                    return Continuation{};
                }
            }

            auto coroutine = copy_and_invalidate(
                (*m_queueReadCopyUpdateSection)[newHead]
            );
            assert_is_valid(coroutine);
            return coroutine;
        }

        enum class steal_mode
        {
            Approximate,
            Precise
        };

        size_t get_tail_to_reserve_from()
        {
            auto tail = m_tail.load(
                std::memory_order_seq_cst
            );
            auto outstandingStealOperations = m_outstandingStealOperations.load(
                std::memory_order_acquire
            );

            if (outstandingStealOperations == 0)
            {
                return tail - 1;
            }

            auto stealingTail = m_stealingTail.load(
                std::memory_order_acquire);
            return stealingTail - 1;
        }

        void start_stealing_from(
            [[maybe_unused]]
            std::unique_lock<std::mutex>& lock,
            size_t tail)
        {
            assert(lock.owns_lock());

            auto outstandingStealOperations = m_outstandingStealOperations.load(
                std::memory_order_acquire
            );

            if (outstandingStealOperations == 0)
            {
                m_stealingTail.store(
                    tail,
                    std::memory_order_relaxed
                );
            }

            m_outstandingStealOperations.fetch_add(
                1,
                std::memory_order_release
            );
        }

        void stop_stealing_from()
        {
            m_outstandingStealOperations.fetch_sub(
                1,
                std::memory_order_relaxed
            );
        }

#ifdef PHANTOM_COROUTINES_DEBUG_INSPECT_STEAL
        static inline thread_local thread_state* steal_other;
        static inline thread_local size_t steal_other_tail;
        static inline thread_local size_t steal_new_other_tail;
        static inline thread_local size_t steal_newOtherHead;
#endif // PHANTOM_COROUTINES_DEBUG_INSPECT_STEAL

        Continuation try_steal(
            thread_state& other,
            steal_mode stealMode
        )
        {
        TryAgainInPreciseMode:
#ifdef PHANTOM_COROUTINES_DEBUG_INSPECT_STEAL
            steal_other = &other;
#endif

            // We can't steal from ourselves!
            if (&other == this)
            {
                return Continuation{};
            }

            std::unique_lock lock{ other.m_mutex, std::defer_lock };
            if (stealMode == steal_mode::Precise)
            {
                lock.lock();
            }

            auto otherTail = other.m_tail.load(std::memory_order_seq_cst);
            auto otherHead = other.m_head.load(std::memory_order_seq_cst);
            if (otherHead <= otherTail)
            {
                return Continuation{};
            }

            if (stealMode == steal_mode::Approximate)
            {
                if (!lock.try_lock())
                {
                    return Continuation{};
                }

                otherHead = other.m_head.load(std::memory_order_seq_cst);
                otherTail = other.m_tail.load(std::memory_order_seq_cst);
                if (otherHead <= otherTail)
                {
                    return Continuation{};
                }
            }

            // We are here, that means we can legitimately steal.
            // We steal half (rounded up) of the items in the source thread.
            other.start_stealing_from(
                lock,
                otherTail);

            size_t sizeToSteal = (otherHead - otherTail + 1) / 2;
            auto newOtherTail = otherTail + sizeToSteal;
            other.m_tail.store(newOtherTail, std::memory_order_seq_cst);

            // It's possible that acquire_local_item has raced with this method,
            // and the other's head is now lower than the tail we published.
            // The other instance will acquire the lock before doing any more
            // processing, and we will adjust the m_outstandingCopyOperationCount
            // and m_tail accordingly.
            auto newOtherHead = other.m_head.load(std::memory_order_seq_cst);
            if (newOtherHead <= otherTail)
            {
                // We have to give back all the items, and do not process anything.
                // However, if we're in precise mode, it's important that we try
                // to steal again.
                other.m_tail.store(otherTail, std::memory_order_seq_cst);
                other.stop_stealing_from();
                if (stealMode == steal_mode::Precise)
                {
                    goto TryAgainInPreciseMode;
                }
                return Continuation{};
            } else if (newOtherHead < newOtherTail)
            {
                // We have to give back some of the items.
                auto newSizeToSteal = newOtherHead - otherTail;
                newOtherTail = newOtherHead;
                
                other.m_tail.store(newOtherTail, std::memory_order_seq_cst);

                sizeToSteal = newSizeToSteal;
            }

#ifdef PHANTOM_COROUTINES_DEBUG_INSPECT_STEAL
            steal_newOtherHead = newOtherHead;
            steal_new_other_tail = newOtherTail;
#endif

            // We no longer need the lock.
            // We've reserved enough space in the queue via m_outstandingCopyOperationCount that
            // we can start a read only queue operation in the source to copy the items
            // into our queue.
            lock.unlock();

            // It's important to grab the otherQueueOperation -after- we have acquired other.m_head,
            // as other.m_head releases the queue update operation.
            auto otherQueueOperation = other.m_queueReadCopyUpdateSection.read();
            auto thisQueueOperation = m_queueReadCopyUpdateSection.update();

            // We copy all but one of the items from the source queue.
            // The last item we return as the item to process.
            auto head = m_head.load(std::memory_order_relaxed);
            auto newHead = head + sizeToSteal - 1;

            reserve_queue_space(
                newHead,
                thisQueueOperation
            );

#ifdef PHANTOM_COROUTINES_DEBUG_INSPECT_STEAL
            steal_other_tail = otherTail;
#endif

            for (auto itemCounter = 0; itemCounter < (sizeToSteal - 1); itemCounter++)
            {
                assert_is_valid((*otherQueueOperation)[otherTail + itemCounter]);
                auto coroutine = copy_and_invalidate((*otherQueueOperation)[otherTail + itemCounter]);


                (*thisQueueOperation)[head + itemCounter] = coroutine;
            }

            // This releases all the copy operations done above.
            m_head.store(newHead, std::memory_order_seq_cst);

            assert_is_valid((*otherQueueOperation)[otherTail + sizeToSteal - 1]);
            auto itemToProcess = copy_and_invalidate((*otherQueueOperation)[otherTail + sizeToSteal - 1]);
            assert_is_valid(itemToProcess);

            other.stop_stealing_from();

            // Now, for all the items we've stolen, it's possible
            // that some other thread B checked this thread A for items to steal,
            // didn't find any, but because we actually stole all the items
            // from yet -another- thread C, thread A contains items 
            // that should cause thread B to wakeup. Thread B will not wake up, though.
            // This is possible for as many threads as there are items we've stolen.
            // -One- of the items we stole we guarantee for ourselves,
            // so we don't have to wake a thread for it.
            auto sleepingThreads = m_scheduler.m_sleepingThreadCount.load(
                std::memory_order_relaxed);
            auto threadsToWake = std::min(sleepingThreads, sizeToSteal - 1);
            auto threadStatesOperation = m_scheduler.m_threadStatesSection.read();
            for (auto wakeupThreadCounter = 0; wakeupThreadCounter < threadsToWake; wakeupThreadCounter++)
            {
                m_scheduler.wake_one_thread(
                    threadStatesOperation);
            }
            return itemToProcess;
        }

        Continuation acquire_remote_item()
        {
            auto threadStatesReadOperation = m_scheduler.m_threadStatesSection.read();

            do
            {
                // First try to acquire something without blocking.
                for (auto& threadState : threadStatesReadOperation->m_threadStates)
                {
                    auto remoteItem = try_steal(
                        **threadState.second,
                        steal_mode::Approximate
                    );
                    if (remoteItem)
                    {
                        return remoteItem;
                    }
                }

                // Now try to acquire something with blocking.
                for (auto& threadState : threadStatesReadOperation->m_threadStates)
                {
                    auto remoteItem = try_steal(
                        **threadState.second,
                        steal_mode::Precise
                    );
                    if (remoteItem)
                    {
                        return remoteItem;
                    }
                }
            }
            while (threadStatesReadOperation.refresh());

            return Continuation{};
        }

        void mark_intent_to_sleep()
        {
            auto previousProcessingState = m_processingState.load(
                std::memory_order_acquire
            );

            ProcessingState nextProcessingState;

            do
            {

                if (previousProcessingState == ProcessingState::Sleeping_StopRequested
                    || previousProcessingState == ProcessingState::Processing_StopRequested)
                {
                    nextProcessingState = previousProcessingState;
                }
                else
                {
                    nextProcessingState = ProcessingState::Sleeping;
                }

            } while (!m_processingState.compare_exchange_strong(
                previousProcessingState,
                nextProcessingState,
                std::memory_order_seq_cst
            ));

            if (previousProcessingState == ProcessingState::Sleeping_StopRequested
                || previousProcessingState == ProcessingState::Processing_StopRequested)
            {
                return;
            }

            bool wasSleeping =
                previousProcessingState == ProcessingState::Sleeping
                ||
                previousProcessingState == ProcessingState::Sleeping_StopRequested;

            if (!wasSleeping)
            {
                m_scheduler.m_sleepingThreadCount.fetch_add(1, std::memory_order_relaxed);
            }
        }
        
        void sleep(
            std::stop_token& stopToken
        )
        {
            if (stopToken.stop_requested())
            {
                return;
            }

            m_processingState.wait(
                ProcessingState::Sleeping,
                std::memory_order_acquire);
        }

        void remove_intent_to_sleep()
        {
            auto threadStatesOperation = m_scheduler.m_threadStatesSection.read();
            m_scheduler.wake_one_thread(threadStatesOperation, this);
        }

        void mark_intent_to_stop_processing()
        {
            auto previousState = m_processingState.load(
                std::memory_order_relaxed
            );
            while (true)
            {
                auto nextState = ProcessingState::Processing_StopRequested;
                if (previousState == ProcessingState::Sleeping)
                {
                    nextState = ProcessingState::Sleeping_StopRequested;
                }

                if (m_processingState.compare_exchange_weak(
                    previousState,
                    nextState,
                    std::memory_order_seq_cst
                ))
                {
                    break;
                }
            }
            m_processingState.notify_all();
        }

        void mark_as_stopped()
        {
            auto previousState = m_processingState.load(
                std::memory_order_acquire
            );

            if (previousState == ProcessingState::Processing
                || previousState == ProcessingState::Processing_StopRequested)
            {
                return;
            }

            remove_intent_to_sleep();
        }

        void process_items(
            std::stop_token stopToken
        )
        {
            ++m_scheduler.m_processingThreadCount;

            {
                ProcessingState expectedProcessingState = ProcessingState::Stopped;

                m_processingState.compare_exchange_strong(
                    expectedProcessingState,
                    ProcessingState::Processing,
                    std::memory_order_seq_cst
                );
            }

#if PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING
            bool isFirstTimeSleeping = true;
            Continuation lastContinuation;
#endif
            std::stop_callback stopCallback
            {
                stopToken,
                [this]
                {
                    mark_intent_to_stop_processing();
                }
            };

            while (!stopToken.stop_requested())
            {
                auto coroutineToResume = acquire_local_item();
                if (!coroutineToResume)
                {
                    coroutineToResume = acquire_remote_item();
                }
                if (!coroutineToResume)
                {
                    mark_intent_to_sleep();
                    coroutineToResume = acquire_remote_item();
                    if (coroutineToResume)
                    {
                        remove_intent_to_sleep();
                    }
                    else
                    {

#if PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING
                        // This allows users to set a breakpoint when all threads are sleeping.
                        if (m_scheduler.m_sleepingThreadCount.load() == m_scheduler.m_processingThreadCount.load()
                            && !isFirstTimeSleeping)
                        {
                            static std::atomic<bool> isAllThreadsSleeping;

                            // Set a breakpoint here to detect when all threads are sleeping.
                            isAllThreadsSleeping.store(true);
                        }
#endif
                        sleep(
                            stopToken);

#if PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING
                        isFirstTimeSleeping = false;
#endif
                    }
                }
                if (coroutineToResume)
                {
                    coroutineToResume.resume();
#if PHANTOM_COROUTINES_THREAD_POOL_SCHEDULER_DETECT_ALL_THREADS_SLEEPING
                    lastContinuation = coroutineToResume;
#endif
                }
            }

            mark_as_stopped();
            --m_scheduler.m_processingThreadCount;
        }
    };

    struct thread_state_list
    {
        std::unordered_map<
            std::thread::id, 
            std::shared_ptr<std::shared_ptr<thread_state>>
        > m_threadStates;
    };

    static inline std::atomic<size_t> m_nextThreadPoolSchedulerId = 1;
    size_t m_threadPoolSchedulerId = m_nextThreadPoolSchedulerId.fetch_add(1, std::memory_order_relaxed);
    std::atomic<size_t> m_sleepingThreadCount;
    std::atomic<size_t> m_processingThreadCount;
    read_copy_update_section<thread_state_list> m_threadStatesSection;
    typedef read_copy_update_section<thread_state_list>::read_operation thread_states_read_operation_type;
    typedef read_copy_update_section<thread_state_list>::update_operation thread_states_update_operation_type;

    std::shared_ptr<thread_state>& get_current_thread_state(
        thread_states_update_operation_type& threadStatesOperation
    )
    {
        // It's likely we're using a single scheduler,
        // so cache the previous result of looking for thread state for this thread.
        static thread_local size_t lastThreadPoolSchedulerId = 0;
        static thread_local std::shared_ptr<thread_state>* lastThreadState = nullptr;

        if (m_threadPoolSchedulerId == lastThreadPoolSchedulerId)
        {
            return *lastThreadState;
        }

        auto iterator = threadStatesOperation->m_threadStates.find(
            std::this_thread::get_id());
        if (iterator != threadStatesOperation->m_threadStates.end())
        {
            lastThreadPoolSchedulerId = m_threadPoolSchedulerId;
            lastThreadState = &*iterator->second;
            return *iterator->second;
        }

        auto threadState = std::make_shared<thread_state>(*this);
        auto threadStatePointer = std::make_shared<std::shared_ptr<thread_state>>(threadState);

        do
        {
            threadStatesOperation.emplace(
                *threadStatesOperation
            );
            threadStatesOperation.replacement().m_threadStates[std::this_thread::get_id()] = threadStatePointer;
        } while (!threadStatesOperation.compare_exchange_strong());

        auto& result = threadStatesOperation->m_threadStates.find(
            std::this_thread::get_id()
        )->second;

        lastThreadPoolSchedulerId = m_threadPoolSchedulerId;
        lastThreadState = &*result;

        return *result;
    }

    std::shared_ptr<thread_state>& get_current_thread_state_expensive()
    {
        auto threadStatesOperation = m_threadStatesSection.update();
        auto& threadState = get_current_thread_state(threadStatesOperation);

        return threadState;
    }

    std::shared_ptr<thread_state>& get_current_thread_state()
    {
        // It's likely we're using a single scheduler,
        // so cache the previous result of looking for thread state for this thread.
        static thread_local size_t lastThreadPoolSchedulerId = 0;
        static thread_local std::shared_ptr<thread_state>* lastThreadState = nullptr;

        if (m_threadPoolSchedulerId != lastThreadPoolSchedulerId)
            [[unlikely]]
        {
            lastThreadState = &get_current_thread_state_expensive();
            lastThreadPoolSchedulerId = m_threadPoolSchedulerId;
        }

        return *lastThreadState;
    }

    void await_suspend(
        Continuation continuation
    )
    {
        if constexpr (is_coroutine_handle<Continuation>)
        {
            assert(continuation);
            assert(!continuation.done());
        }

        auto threadStatesOperation = m_threadStatesSection.update();
        auto& threadState = get_current_thread_state(threadStatesOperation);
        threadState->enqueue(continuation);
        wake_one_thread(threadStatesOperation);
    }

    void wake_one_thread(
        thread_states_read_operation_type& threadStatesOperation,
        thread_state* preferredThread = nullptr
    )
    {
        // An enqueue operation used seq_cst on m_head.
        // Before a thread was allowed to sleep, it incremented m_sleepingThreadCount
        // and then did seq_cst operations on all the m_head items.
        // Therefore, m_sleepingThreadCount will read a non-zero value
        // if there is some thread attempting to sleep,
        // and we do not need to do the compare_exchange.
        auto sleepingThreadCount = m_sleepingThreadCount.load(std::memory_order_relaxed);
        do
        {
            if (sleepingThreadCount == 0)
            {
                return;
            }
        } while (!m_sleepingThreadCount.compare_exchange_weak(
            sleepingThreadCount,
            sleepingThreadCount - 1,
            std::memory_order_relaxed,
            std::memory_order_relaxed
        ));

        if (preferredThread
            && preferredThread->try_wake())
        {
            return;
        }

        while (true)
        {
            for (auto& threadState : threadStatesOperation.value().m_threadStates)
            {
                if ((*threadState.second)->try_wake())
                {
                    return;
                }
            }
            threadStatesOperation.refresh();
        }
    }

    class awaiter
    {
        friend class basic_thread_pool_scheduler;
        basic_thread_pool_scheduler& m_scheduler;

        awaiter(
            basic_thread_pool_scheduler& scheduler
        ) : m_scheduler { scheduler }
        {}

    public:
        bool await_ready() const noexcept
        {
            return false;
        }

        void await_suspend(
            Continuation continuation
        )
        {
            m_scheduler.await_suspend(continuation);
        }

        void await_resume() const noexcept
        {}
    };

public:
    awaiter schedule() noexcept
    {
        return awaiter{ *this };
    }

    void process_items(
        std::stop_token stopToken
    )
    {
        auto threadState = get_current_thread_state();
        threadState->process_items(
            stopToken
        );
    }
};

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::thread_pool_scheduler;
}
#endif
