#pragma once

#include <atomic>
#include <concepts>
#include <memory>
#include <ranges>
#include <thread>
#include <unordered_map>
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
	typename Value
>
class read_copy_update_section
	:
private immovable_object
{
	typedef size_t epoch_type;

	typedef Value value_type;
	typedef std::remove_const_t<Value> mutable_value_type;

	struct value_holder
	{
		epoch_type m_epoch;
		mutable_value_type m_value;

		value_holder(
			auto&&... args
		) : m_value { std::forward<decltype(args)>(args)... }
		{}
	};

	typedef std::shared_ptr<value_holder> value_holder_ptr;
	typedef std::atomic<value_holder_ptr> atomic_value_holder_ptr;

	std::atomic<epoch_type> m_epoch;
	atomic_value_holder_ptr m_value;

	class operation
		:
		protected assert_same_thread,
		private immovable_object
	{

	protected:
		typedef std::unordered_map<read_copy_update_section*, value_holder_ptr> value_map;
		typedef std::unordered_multimap<value_holder*, operation*> pending_operations_map;
		inline static thread_local value_map m_threadLocalValues;
		inline static thread_local pending_operations_map m_threadLocalSoftOperations;

		read_copy_update_section& m_section;
		
		pending_operations_map::iterator m_threadLocalSoftOperationsEntry;

		value_holder* m_valueHolderSoftReference;
		value_holder_ptr m_valueHolderHardReference;

		operation(
			read_copy_update_section& section
		)
			:
			m_section{ section }
		{
			// We explicitly don't use try_emplace here
			// so that we don't incur the expensive shared_ptr load operation
			// at m_value.load
			auto threadValueMapEntry = m_threadLocalValues.find(&section);

			if (threadValueMapEntry == m_threadLocalValues.end())
			{
				threadValueMapEntry = m_threadLocalValues.insert(std::make_pair(
					&section,
					m_section.m_value.load(
						std::memory_order_acquire
					)))
					.first;
			}

			// If the current epoch has changed, then the thread local value map contains an obsolete value.
			if (threadValueMapEntry->second->m_epoch != m_section.m_epoch.load(std::memory_order_acquire))
			{
				// The thread local value map contains an obsolete value.
				// We want to replace it with the up-to-date value, but before we do so
				// we need to make sure any other pending operations on this thread
				// are correctly reference counting the value.
				// So find all the existing operations on the same epoch and grant
				// them hard references to the value_holder.
				auto operationsOnThisEpoch = m_threadLocalSoftOperations.equal_range(
					threadValueMapEntry->second.get()
				);

				for (auto& operation : std::ranges::subrange(operationsOnThisEpoch.first, operationsOnThisEpoch.second))
				{
					operation.second->m_valueHolderHardReference = threadValueMapEntry->second;
				}

				// Now we can replace the thread-local map entry with the current value.
				threadValueMapEntry->second = m_section.m_value.load(
					std::memory_order_acquire);
			}

			m_valueHolderSoftReference = threadValueMapEntry->second.get();
			m_threadLocalSoftOperationsEntry = m_threadLocalSoftOperations.insert(
				std::make_pair(
					m_valueHolderSoftReference,
					this
				));
		}

		~operation()
		{
			if (m_threadLocalSoftOperationsEntry != m_threadLocalSoftOperations.end())
			{
				m_threadLocalSoftOperations.erase(
					m_threadLocalSoftOperationsEntry);
			}
		}

	public:
		Value& value()
		{
			check_thread();
			return m_valueHolderSoftReference->m_value;
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
		value_holder_ptr m_replacementValueHolder = nullptr;

	public:
		update_operation(
			read_copy_update_section& section
		) :
			operation{ section }
		{}

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
			m_replacementValueHolder = std::make_shared<value_holder>(
				std::forward<decltype(args)>(args)...
				);
			
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
			
			m_replacementValueHolder->m_epoch = operation::m_section.m_epoch.fetch_add(1, std::memory_order_relaxed);

			// To atomically swap out a shared_ptr,
			// we need to have one in hand. Unfortunately,
			// that means locking and acquiring a copy here
			// before doing the actual compare_exchange_strong.
			// We'll optimize this another day; writes are expected to
			// be infrequent in this data structure.
			if (operation::m_valueHolderHardReference.get() != operation::m_valueHolderSoftReference)
			{
				operation::m_valueHolderHardReference = operation::m_section.m_value.load(
					std::memory_order_relaxed
				);

				if (operation::m_threadLocalSoftOperationsEntry != operation::m_threadLocalSoftOperations.end())
				{
					operation::m_threadLocalSoftOperations.erase(
						operation::m_threadLocalSoftOperationsEntry);
					operation::m_threadLocalSoftOperationsEntry = operation::m_threadLocalSoftOperations.end();
				}
			}

			auto result = operation::m_section.m_value.compare_exchange_strong(
				operation::m_valueHolderHardReference,
				m_replacementValueHolder,
				std::memory_order_acq_rel,
				std::memory_order_acquire
			);

			if (result)
			{
				operation::m_valueHolderHardReference = std::move(m_replacementValueHolder);
			}
			operation::m_valueHolderSoftReference = operation::m_valueHolderHardReference.get();

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
			return m_replacementValueHolder->m_value;
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
	) :
		m_value
	{ std::make_shared<value_holder>(
			std::forward<decltype(args)>(args)...) 
	}
	{
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
