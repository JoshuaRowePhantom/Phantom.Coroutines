#pragma once

#include "detail/atomic_state.h"
#include "detail/coroutine.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "awaiter_list.h"
#include <type_traits>

namespace Phantom::Coroutines
{
namespace detail
{

template<
	is_await_cancellation_policy WaitCancellationPolicy,
	is_continuation Continuation
>
class basic_async_mutex;

template<
	typename T
> concept is_async_mutex_policy =
is_await_cancellation_policy<T>
|| is_await_result_on_destruction_policy<T>
|| is_awaiter_cardinality_policy<T>
|| is_continuation_type_policy<T>;

template<
	is_async_mutex_policy ... Policy
> using async_mutex = basic_async_mutex<
	select_await_cancellation_policy<Policy..., await_is_not_cancellable>,
	select_continuation_type<Policy..., default_continuation_type>
>;

template<
	is_await_cancellation_policy AwaitCancellationPolicy,
	is_continuation Continuation
>
class basic_async_mutex
	:
private immovable_object,
private awaiter_list_mutex<AwaitCancellationPolicy>
{
public:
	using lock_type = std::unique_lock<basic_async_mutex>;

private:
	struct UnlockedState {};
	struct LockedState;

	class [[nodiscard]] async_mutex_lock_operation
		:
		private immovable_object
	{
		friend class basic_async_mutex;

		union
		{
			basic_async_mutex* m_mutex;
			async_mutex_lock_operation* m_nextAwaiter;
		};

		coroutine_handle<> m_continuation;

		async_mutex_lock_operation(
			basic_async_mutex* mutex
		) :
			m_mutex(mutex)
		{}

	public:
		bool await_ready() const noexcept { return false; }

		bool await_suspend(
			coroutine_handle<> continuation
		) noexcept
		{
			m_continuation = continuation;

			// We destroy m_mutex when we set m_nextAwaiter,
			// so copy it here.
			basic_async_mutex* mutex = m_mutex;

			auto nextStateLambda = [&](
				state_type previousState
				) -> state_type
			{
				if (previousState == UnlockedState{})
				{
					return LockedNoWaitersState;
				}

				m_nextAwaiter = previousState.as<LockedState>();
				return this;
			};

			auto previousState = compare_exchange_weak_loop(
				mutex->m_state,
				nextStateLambda
			);

			return previousState != UnlockedState{};
		}

		void await_resume() noexcept 
		{
		}
	};

	class [[nodiscard]] async_mutex_scoped_lock_operation
		:
		private immovable_object
	{
		friend class basic_async_mutex;

		basic_async_mutex& m_mutex;
		async_mutex_lock_operation m_lockOperation;

		async_mutex_scoped_lock_operation(
			basic_async_mutex& mutex
		) :
			m_mutex{mutex},
			m_lockOperation{mutex}
		{}

	public:
		bool await_ready() const noexcept 
		{ 
			return m_lockOperation.await_ready(); 
		}

		bool await_suspend(
			coroutine_handle<> continuation
		) noexcept
		{
			return m_lockOperation.await_suspend(
				continuation);
		}

		[[nodiscard]] lock_type await_resume() noexcept
		{
			return lock_type { m_mutex, std::adopt_lock };
		}
	};

	typedef atomic_state<
		SingletonState<UnlockedState>,
		StateSet<LockedState, async_mutex_lock_operation*>
	> atomic_state_type;
	typedef atomic_state_type::state_type state_type;

	static inline const state_type LockedNoWaitersState = nullptr;

	atomic_state_type m_state = UnlockedState{};
	async_mutex_lock_operation* m_waiters = nullptr;

public:
	bool try_lock() noexcept
	{
		state_type expectedState = UnlockedState{};
		return m_state.compare_exchange_strong(
			expectedState,
			LockedNoWaitersState,
			std::memory_order_acquire
		);
	}

	[[nodiscard]] lock_type try_scoped_lock() noexcept
	{
		if (try_lock())
		{
			return lock_type{ *this, std::adopt_lock };
		}
		else
		{
			return lock_type{};
		}
	}

	async_mutex_lock_operation lock()  noexcept
	{
		return async_mutex_lock_operation{ this };
	}

	async_mutex_scoped_lock_operation scoped_lock() noexcept
	{
		return async_mutex_scoped_lock_operation{ this };
	}

	void unlock() noexcept
	{
		// We desire to service awaiters in order that they requested awaiting.
		// This prevents starvation.
		// We maintain the ordered list in m_waiters;
		// when that empties out, we copy the atomically added awaiters into
		// m_waiters.

		// Question: do we have to memory_order_acquire something here
		// to ensure m_waiters is correct?
		if (!m_waiters)
		{
			state_type previousState = LockedNoWaitersState;

			// See if we can atomically determine there are no more waiters in the atomic
			// and unlock.
			if (m_state.compare_exchange_strong(
				previousState,
				UnlockedState{},
				std::memory_order_release
			))
			{
				// There are no other waiters and we're now unlocked.
				return;
			}

			// Otherwise, grab all the current waiters and put them in m_waiters in reverse order.
			// No other thread will be attempting to do an unlock at the same time, so
			// we'll gain exclusive ownership of the linked list of waiters.
			auto waiter = m_state.exchange(
				LockedNoWaitersState,
				std::memory_order_acquire
			).as<LockedState>();

			while (waiter)
			{
				auto nextWaiter = waiter->m_nextAwaiter;
				waiter->m_nextAwaiter = m_waiters;
				m_waiters = waiter;
				waiter = nextWaiter;
			}
		}

		auto waiter = m_waiters;
		assert(waiter != nullptr);
		m_waiters = m_waiters->m_nextAwaiter;

		// Question: do we have to memory_order_release something here
		// to ensure m_waiters is correct?

		// This has the potential to overflow the stack.
		// We expect callers to be using suspend_result.
		waiter->m_continuation.resume();
		return;
	}
};

}

using detail::async_mutex;

}
