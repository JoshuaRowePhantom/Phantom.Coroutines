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
		Value m_value;

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
		read_copy_update_section& m_section;
		bool m_previousIsPerformingOperation;
		list_entry* m_listEntry;
	protected:
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
		Value* operator->()
		{
			check_thread();
			return &m_listEntry->m_value;
		}

		Value& operator*()
		{
			return *operator->();
		}
	};

	class read_operation 
		:
	public operation
	{
	public:
		read_operation(
			read_copy_update_section& section,
			constructor_tag = {}
		) :
			operation{ section }
		{}
	};

	class write_operation
		:
		public operation
	{
	public:
		write_operation(
			read_copy_update_section& section,
			constructor_tag = {}
		) :
			operation{ section }
		{}

		template<
			typename AssignValue
		>
		[[nodiscard]]
		bool operator=(AssignValue&& value)
		{
			operation::check_thread();
			throw 1;
		}

		template<
			typename ... Args
		>
		[[nodiscard]]
		bool emplace(
			Args&&... args
		)
		{
			operation::check_thread();
			throw 1;
		}
	};

public:
	read_copy_update_section(
		auto&&... args
	)
	{
		m_listHead = new list_entry
		{
			std::forward<decltype(args)>(args)...
		};
	}

	read_operation read() const
	{
		return read_operation{ const_cast<read_copy_update_section&>(*this) };
	}

	write_operation write()
	{
		return write_operation{ *this };
	}
};

}
}
