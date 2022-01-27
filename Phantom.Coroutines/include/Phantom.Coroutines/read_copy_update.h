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
		Value& value()
		{
			check_thread();
			return m_listEntry->m_value;
		}
	};

public:

	class read_operation
		:
		private operation
	{
	public:
		read_operation(
			const read_copy_update_section& section
		) :
			operation{ const_cast<read_copy_update_section&>(section) }
		{}

		using operation::value;

		// Read the value of the read_copy_update_section as
		// of the time the operation was started.
		Value* operator->()
		{
			return &value();
		}

		// Read the value of the read_copy_update_section as
		// of the time the operation was started.
		Value& operator*()
		{
			return value();
		}
	};

	class update_operation
		:
		private operation
	{
		list_entry* m_replacementListEntry = nullptr;

	public:
		update_operation(
			read_copy_update_section& section
		) :
			operation{ section }
		{}

		~update_operation()
		{
			delete m_replacementListEntry;
		}

		using operation::value;

		// Set the value to replace with.
		decltype(auto) operator=(
			auto&& value
			)
		{
			return (emplace(
				std::forward<decltype(value)>(value)
			));
		}

		// Set the value to replace with.
		decltype(auto) emplace(
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

			return (replacement());
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
				std::memory_order_acq_rel,
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
	private update_operation
	{
	public:
		write_operation(
			read_copy_update_section& section
		) :
			update_operation{ section }
		{}

		using update_operation::value;

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
			update_operation::emplace(
				std::forward<decltype(args)>(args)...
			);

			update_operation::exchange();

			return update_operation::value();
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

	// Read the current value stored in the section.
	// The value is only valid for the duration
	// of the expression.
	[[nodiscard]] read_operation operator->() const
	{
		return read();
	}

	// Read the current value stored in the section.
	[[nodiscard]] read_operation read() const
	{
		return read_operation
		{ 
			const_cast<read_copy_update_section&>(*this) 
		};
	}

	// Begin an operation to read / modify / write
	// the value stored in the section, with update
	// race detection.
	// 
	// A typical use is:
	// 
	// void AddEntryToMap(std::string key, std::string value)
	// {
	//	read_copy_update_section<std::map<std::string, std::string>> section;
	//	auto operation = section.update();
	//  
	// // Start by copying the original map.
	//  operation.emplace(operation.value());
	//  // Add the key / value of interest
	//  operation.replacement()[key] = value;
	// 
	//  while (!operation.compare_exchange_strong())
	//  {
	//	   // If we fail to perform the replacement, then our updated map
	//	   // is missing some entries or has some out of date entries.
	//	   // Rather than copy the map over again, we modify it in-place,
	//	   // as there are likely only a few entries updated. A better algorithm
	//	   // iterates over both maps in parallel.
	//     for(auto value : operation.value())
	//     {
	//        if (!operation.replacement().contains(value.first)
	//            || operation.replacement()[value.first] != value.second)
	//        {
	//            operation.replacement()[value.first] = value.second;
	//        }
	//     }
	//	   operation.replacement()[key] = value;
	//  }
	// }
	[[nodiscard]] update_operation update()
	{
		return update_operation
		{
			*this
		};
	}

	// Begin an operation to read / modify / write
	// the value stored in the section.
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
