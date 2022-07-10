export module Phantom.Coroutines.async_mutex;

import Phantom.Coroutines.atomic_state;
import Phantom.Coroutines.coroutine;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.non_copyable;
import <assert.h>;
import <type_traits>;

namespace Phantom::Coroutines
{

export class async_mutex_lock;

export class async_mutex
	:
private immovable_object
{
	struct UnlockedState {};
	struct LockedState;

	class async_mutex_lock_operation
		:
		private immovable_object
	{
		friend class async_mutex;

		union
		{
			async_mutex* m_mutex;
			async_mutex_lock_operation* m_nextAwaiter;
		};

		coroutine_handle<> m_continuation;

		async_mutex_lock_operation(
			async_mutex* mutex
		) :
			m_mutex(mutex)
		{}

	public:
		bool await_ready() const noexcept { return false; }

		bool await_suspend(
			coroutine_handle<> continuation
		) noexcept;

		void await_resume() noexcept 
		{
		}
	};

	class async_mutex_scoped_lock_operation
	{
		friend class async_mutex;

		async_mutex* m_mutex;
		async_mutex_lock_operation m_lockOperation;

		async_mutex_scoped_lock_operation(
			async_mutex* mutex
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

		async_mutex_lock await_resume() noexcept;
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

	async_mutex_lock try_scoped_lock() noexcept;

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

class async_mutex_lock
	:
private noncopyable
{
	friend class async_mutex;
	async_mutex* m_mutex;

	async_mutex_lock(
		async_mutex* mutex
	)
		: m_mutex { mutex }
	{}

public:
	async_mutex_lock(
	)  noexcept :
		m_mutex { nullptr }
	{}

	async_mutex_lock(
		async_mutex_lock&& other
	) noexcept
	{
		m_mutex = other.m_mutex;
		other.m_mutex = nullptr;
	}

	async_mutex_lock& operator =(
		async_mutex_lock&& other
		) noexcept
	{
		if (this == &other)
		{
			return *this;
		}

		release();
		m_mutex = other.m_mutex;
		other.m_mutex = nullptr;
		return *this;
	}

	void release() noexcept
	{
		if (m_mutex)
		{
			m_mutex->unlock();
			m_mutex = nullptr;
		}
	}

	explicit operator bool() const
	{
		return m_mutex;
	}

	~async_mutex_lock() noexcept
	{
		release();
	}
};

inline bool async_mutex::async_mutex_lock_operation::await_suspend(
	coroutine_handle<> continuation
	) noexcept
{
	m_continuation = continuation;

	// We destroy m_mutex when we set m_nextAwaiter,
	// so copy it here.
	async_mutex* mutex = m_mutex;

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

inline async_mutex_lock async_mutex::async_mutex_scoped_lock_operation::await_resume() noexcept
{
	return async_mutex_lock{ m_mutex };
}

inline async_mutex_lock async_mutex::try_scoped_lock() noexcept
{
	if (try_lock())
	{
		return async_mutex_lock{ this };
	}
	else
	{
		return async_mutex_lock{};
	}
}
}
