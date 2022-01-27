#pragma once

#include <atomic>
#include <concepts>
#include <memory>
#include "detail/assert_same_thread.h"
#include "detail/scope_guard.h"
#include "detail/immovable_object.h"

namespace Phantom::Coroutines
{
namespace detail
{

class ReadCopyUpdate_CleanupOnWrite
{};

class ReadCopyUpdate_CleanupOnReadOrWrite
{};

template<
	typename TReadCopyUpdateCleaner
> concept ReadCopyUpdateCleaner =
	std::same_as<TReadCopyUpdateCleaner, ReadCopyUpdate_CleanupOnWrite>
	||
	std::same_as<TReadCopyUpdateCleaner, ReadCopyUpdate_CleanupOnReadOrWrite>;

template<
	typename Value,
	ReadCopyUpdateCleaner CleanupPolicy = ReadCopyUpdate_CleanupOnReadOrWrite
>
class read_copy_update_section
	:
private immovable_object
{
	struct list_entry
	{
		size_t m_epoch;
		list_entry* m_next;
		std::remove_const_t<Value> m_value;

		list_entry(
			auto&&... args
		) :
			m_value{ std::forward<decltype(args)>(args)...}
		{}
	};

	struct thread_state
	{
		std::atomic<bool> m_previousIsPerformingOperation;
	};

	struct thread_guard
	{
		thread_state m_threadState;
	};

	inline static std::atomic<size_t> m_globalEpoch = 0;
	inline static thread_local thread_guard m_threadGuard;

	std::atomic<list_entry*> m_listHead = nullptr;

	class constructor_tag {};

	class operation
		:
		protected assert_same_thread,
		private immovable_object
	{
	protected:
		read_copy_update_section& m_section;
		bool m_previousIsPerformingOperation;
		list_entry* m_listEntry;

		operation(
			read_copy_update_section& section
		)
			:
			m_section{ section },
			m_previousIsPerformingOperation{ m_threadGuard.m_threadState.m_previousIsPerformingOperation },
			m_listEntry{ section.m_listHead }
		{}

		~operation()
		{
			if (m_previousIsPerformingOperation)
			{
				return;
			}
			//m_threadGuard.threadState.m_previousIsPerformingOperation = m_previousIsPerformingOperation;
		}

	public:
		// Read the value of the read_copy_update_section as
		// of the time the operation was started.
		Value* operator->()
		{
			check_thread();
			return &m_listEntry->m_value;
		}

		// Read the value of the read_copy_update_section as
		// of the time the operation was started.
		Value& operator*()
		{
			return *operator->();
		}
	};

public:

	class read_operation
		:
		private operation
	{
	public:
		read_operation(
			read_copy_update_section& section,
			constructor_tag = {}
		) :
			operation{ section }
		{}

		using operation::operator->;
		using operation::operator*;
	};

	class exchange_operation
		:
		private operation
	{
		list_entry* m_replacementListEntry = nullptr;

	public:
		exchange_operation(
			read_copy_update_section& section,
			constructor_tag = {}
		) :
			operation{ section }
		{}

		~exchange_operation()
		{
			delete m_replacementListEntry;
		}

		using operation::operator->;
		using operation::operator*;

		// Set the value to replace with.
		exchange_operation& operator=(
			auto&& value
			)
		{
			return emplace(
				std::forward<decltype(value)>(value)
			);
		}

		// Set the value to replace with.
		exchange_operation& emplace(
			auto&&... args
		)
		{
			delete m_replacementListEntry;
			// Important to set to null in case "new" throws.
			m_replacementListEntry = nullptr;
			m_replacementListEntry = new list_entry
			{
				std::forward<decltype(args)>(args)...
			};

			return *this;
		}

		// Perform the exchange.
		// using the value that was assigned or emplaced.
		// If there was no previous assignment or emplacement, behavior is undefined.
		// The value of the operator-> and operator* will be
		// updated to the new replacement value.
		void exchange()
		{
			while (!compare_exchange_strong()) {}
		}

		// Conditionally perform the exchange.
		// using the value that was assigned or emplaced.
		// If there was no previous assignment or emplacement, behavior is undefined.
		// The value of the operator-> and operator* will be
		// updated to the new replacement value if successful, 
		// or to the current value of the read_copy_update_section if failed.
		// Returns true if the exchange was successful, false if the exchange failed.
		[[nodiscard]]
		bool compare_exchange_strong()
		{
			operation::check_thread();
			
			m_replacementListEntry->m_next = operation::m_listEntry;

			auto result = operation::m_section.m_listHead.compare_exchange_strong(
				operation::m_listEntry,
				m_replacementListEntry,
				std::memory_order_release,
				std::memory_order_acquire
			);

			if (result)
			{
				operation::m_listEntry = m_replacementListEntry;
				m_replacementListEntry = nullptr;
			}

			return result;
		}

		// Obtain the value created by the previous operator=
		// or emplace operation. If there was no previous operation,
		// behavior is undefined.  If a previous exchange or compare_exchange
		// succeeded, the behavior is undefined.
		[[nodiscard]]
		std::remove_const_t<Value>& replacement()
		{
			operation::check_thread();
			return m_replacementListEntry->m_value;
		}
	};

	class write_operation
		:
	private exchange_operation
	{
	public:
		write_operation(
			read_copy_update_section& section,
			constructor_tag = {}
		) :
			exchange_operation{ section }
		{}

		using exchange_operation::operator->;
		using exchange_operation::operator*;

		Value& operator=(
			auto&& value
			)
		{
			return emplace(
				std::forward<decltype(value)>(value)
			);
		}


		Value& emplace(
			auto&&... args
		)
		{
			exchange_operation::emplace(
				std::forward<decltype(args)>(args)...
			).exchange();

			return **this;
		}
	};

	read_copy_update_section(
		auto&&... args
	)
	{
		m_listHead = new list_entry
		{
			std::forward<decltype(args)>(args)...
		};
	}

	[[nodiscard]] read_operation operator->() const
	{
		return read();
	}

	[[nodiscard]] read_operation read() const
	{
		return read_operation
		{ 
			const_cast<read_copy_update_section&>(*this) 
		};
	}

	[[nodiscard]] exchange_operation exchange()
	{
		return exchange_operation
		{
			*this
		};
	}

	[[nodiscard]] write_operation write()
	{
		return write_operation{ *this };
	}

	// Unconditionally replace the stored value.
	// If this thread loses any races, the operation
	// is retried until it succeeds.
	void emplace(
		auto&&... args
	)
	{
		auto operation = write();
		operation.emplace(
			std::forward<decltype(args)>(args)...
		);
	}
};

}
}
