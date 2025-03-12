#pragma once

#include <concepts>
#include <functional>
#include <memory>
#include <set>
#include <type_traits>
#include <vector>
#include "detail/consecutive_thread_id.h"
#include "reusable_consecutive_global_id.h"

namespace Phantom::Coroutines
{
namespace detail
{
template<
    typename T
>
class atomic_vector
{
public:
    using value_type = T;
    using vector = std::vector<T>;
    using vector_ptr = std::shared_ptr<vector>;

private:
    using atomic_vector_ptr = std::atomic<vector_ptr>;

    atomic_vector_ptr m_atomicVector;

public:
    // Exponentially grow the vector to at least
    // the specified size.
    vector_ptr grow(
        size_t size
    )
    {
        auto oldVector = m_atomicVector.load();
        std::shared_ptr<std::vector<T>> newVector;
        do
        {
            if (oldVector
                &&
                oldVector->size() >= size)
            {
                return oldVector;
            }

            newVector = std::make_shared<std::vector<T>>(
                std::max(
                    size,
                    oldVector ? oldVector->size() * 2 : 10
                )
            );

            if (oldVector)
            {
                newVector = std::make_shared<std::vector<T>>(
                    std::max(
                        size,
                        oldVector->size() * 2
                    )
                );

                std::copy(
                    oldVector->begin(),
                    oldVector->end(),
                    newVector->begin());
            }
            else
            {
                newVector = std::make_shared<std::vector<T>>(size);
            }
        } while (!m_atomicVector.compare_exchange_weak(
            oldVector,
            newVector));

        return newVector;
    }

    vector_ptr set(
        size_t index,
        auto&& value
    )
    {
        vector_ptr vector;

        do
        {
            vector = grow(
                index + 1);

            (*vector)[index] = value;
        } while (!m_atomicVector.compare_exchange_weak(
            vector,
            vector));

        return vector;
    }

    auto load()
    {
        return m_atomicVector.load();
    }
};

template<
    typename Value
>
class thread_local_storage
{
    reusable_consecutive_global_id<
        struct thread_local_storage_id_label
    > m_threadLocalStorageId;
    
    struct value_holder
    {
        Value m_value;

        value_holder(
            auto& initializer
        ) :
            m_value{ initializer() }
        {
        }
    };

    class thread_state
    {
        using value_ptr = std::shared_ptr<value_holder>;
        using atomic_hard_vector_ptr = atomic_vector<value_ptr>;
        using hard_vector_ptr = typename atomic_hard_vector_ptr::vector_ptr;
        using atomic_soft_vector_ptr = atomic_vector<Value*>;
        using soft_vector_ptr = typename atomic_soft_vector_ptr::vector_ptr;

        const size_t m_threadId = consecutive_thread_id::current();

        // m_hardVector contains hard references to contained values.
        atomic_hard_vector_ptr m_atomicHardVector;

        // This is a non-atomic alias for m_atomicHardVector.
        // The owning thread can access m_hardVector,
        // but non-owning threads have to access m_atomicHardVector.
        hard_vector_ptr m_hardVector;

        // m_softVector contains weak references to contained values,
        // with one less level of indirection than m_hardVector.
        atomic_soft_vector_ptr m_atomicSoftVector;
        soft_vector_ptr m_softVector;

        [[msvc::noinline]]
        Value& add_value(
            size_t threadLocalStorageId,
            auto& initializer
        )
        {
            auto newValue = std::make_shared<value_holder>(
                initializer);

            m_hardVector = m_atomicHardVector.set(
                threadLocalStorageId,
                newValue
            );

            auto softNewValue = std::addressof(newValue->m_value);

            m_softVector = m_atomicSoftVector.set(
                threadLocalStorageId,
                softNewValue);

            return *softNewValue;
        }

    public:
        auto thread_id() const
        {
            return m_threadId;
        }

        // Reset a value.
        // This can be called from another thread.
        void reset(
            size_t threadLocalStorageId
        )
        {
            auto hardVector = m_atomicHardVector.load();
            if (hardVector && hardVector->size() > threadLocalStorageId)
            {
                (*hardVector)[threadLocalStorageId] = nullptr;
            }
            auto softVector = m_atomicSoftVector.load();
            if (softVector && softVector->size() > threadLocalStorageId)
            {
                (*softVector)[threadLocalStorageId] = nullptr;
            }
        }

        // Get the value for the current thread for the given thread id.
        Value& get(
            size_t threadLocalStorageId,
            auto& initializer
        )
        {
            Value* softValue = nullptr;
            if (m_softVector
                &&
                m_softVector->size() > threadLocalStorageId
                ) [[likely]]
            {
                softValue = (*m_softVector)[threadLocalStorageId];
            }
            if (softValue) [[likely]]
            {
                return *softValue;
            }

            return add_value(
                threadLocalStorageId,
                initializer);
        }

        Value& set(
            size_t threadLocalStorageId,
            auto&& initializer
        )
        {
            return add_value(
                threadLocalStorageId,
                initializer
            );
        }
    };

    struct locked_all_threads
    {
        std::unique_lock<std::mutex> lock;
        std::vector<std::shared_ptr<thread_state>>& vector;
    };

    static locked_all_threads get_locked_all_threads()
    {
        static std::mutex mutex;
        static std::vector<std::shared_ptr<thread_state>> allThreads;

        return 
        {
            std::unique_lock{ mutex },
            allThreads
        };
    }
    
    [[msvc::noinline]]
    thread_state& get_thread_state_expensive()
    {
        struct global_setter
        {
            std::shared_ptr<thread_state> m_threadState
                = std::make_shared<thread_state>();

            global_setter()
            {
                locked_all_threads allThreads = get_locked_all_threads();
                allThreads.vector.resize(
                    std::max(
                        allThreads.vector.size(),
                        m_threadState->thread_id() + 1
                    )
                );
                allThreads.vector[
                    m_threadState->thread_id()
                ] = m_threadState;
            }

            ~global_setter()
            {
                locked_all_threads allThreads = get_locked_all_threads();
                allThreads.vector[
                    m_threadState->thread_id()
                ] = nullptr;
            }
        };

        static thread_local global_setter threadStateSetter;
        return *threadStateSetter.m_threadState;
    }

    thread_state& get_thread_state()
    {
        static thread_local thread_state* threadStatePointer = nullptr;

        if (!threadStatePointer)
        {
            threadStatePointer = &get_thread_state_expensive();
        }

        return *threadStatePointer;
    }

    const std::function<Value()> m_initializer;

public:
    using value_type = Value;

    template<
        std::invocable<> Initializer
    >
    requires std::constructible_from<
        Value,
        std::invoke_result_t<Initializer>>
    thread_local_storage(
        Initializer&& initializer
    ) 
        :
        m_initializer{ std::forward<Initializer>(initializer) }
    {
    }

    template<
        typename ... Args
    >
    requires std::constructible_from<
        Value,
        Args...
    >
    thread_local_storage(
        Args&& ... args
    ) :
        m_initializer([args...]() { return Value(args ...); })
    { }

    ~thread_local_storage()
    {
        // Copy the current set of all threads so that we
        // can release the individual thread values outside of a lock.
        locked_all_threads lockedAllThreads = get_locked_all_threads();
        auto allThreads = lockedAllThreads.vector;
        lockedAllThreads.lock.unlock();

        for (auto& threadState : allThreads)
        {
            if(threadState)
            {
                threadState->reset(m_threadLocalStorageId);
            }
        }
    }

    Value& get()
    {
        return get_thread_state().get(
            m_threadLocalStorageId,
            m_initializer);
    }

    const Value& get() const
    {
        return get_thread_state().get(
            m_threadLocalStorageId,
            m_initializer);
    }

    Value* operator->()
    {
        return &get();
    }
    
    const Value* operator->() const
    {
        return &get();
    }

    template<
        typename ... Args
    >
    Value& emplace(
        Args&&... args
    )
        requires std::constructible_from<Value, Args...>
    {
        return get_thread_state().set(
            m_threadLocalStorageId,
            [&]() { return Value(std::forward<Args>(args)...); }
        );
    }

    template<
        typename Other
    >
    Value& operator=(
        Other&& other
        )
        requires std::assignable_from<Value, Other&&>
    {
        get() = std::forward<Other>(other);
        return *this;
    }
};

}

using detail::thread_local_storage;

}