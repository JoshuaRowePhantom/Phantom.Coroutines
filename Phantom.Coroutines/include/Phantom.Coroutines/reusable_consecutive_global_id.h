#pragma once

#include <atomic>
#include <cstddef>

namespace Phantom::Coroutines
{
namespace detail
{

struct reusable_consecutive_global_id_default_increment
{
	template<typename T>
	auto operator()(T& t)
	{
		return t.fetch_add(1, std::memory_order_relaxed);
	}
};

template<
	typename Label,
	typename Value = std::size_t,
	const Value InitialValue = 0,
	typename Increment = reusable_consecutive_global_id_default_increment
>
class reusable_consecutive_global_id
{
	struct reusable_id
	{
		reusable_id* m_next;
		Value m_value;
	};

	inline static std::atomic<Value> m_globalValue = InitialValue;
	inline static std::atomic<reusable_id*> m_reusableIds;
	inline static Increment m_increment;

	reusable_id* m_reusableId;

public:
	reusable_consecutive_global_id()
	{
		auto reusableId = m_reusableIds.load(
			std::memory_order_acquire
		);

		do
		{
			if (!reusableId)
			{
				m_reusableId = new reusable_id
				{
					.m_next = nullptr,
					.m_value = m_increment(m_globalValue)
				};
				break;
			}

			if (m_reusableIds.compare_exchange_weak(
				reusableId,
				reusableId->m_next,
				std::memory_order_acquire,
				std::memory_order_relaxed
			))
			{
				m_reusableId = reusableId;
			}

		} while (!m_reusableId);
	}

	reusable_consecutive_global_id(
		const reusable_consecutive_global_id&
	) = delete;

	reusable_consecutive_global_id(
		reusable_consecutive_global_id&& other
	) :
		m_reusableId { other.m_reusableId }
	{
		other.m_reusableId = nullptr;
	}

	~reusable_consecutive_global_id()
	{
		if (!m_reusableId)
		{
			return;
		}

		m_reusableId->m_next = m_reusableIds.load(
			std::memory_order_relaxed
		);

		while (!m_reusableIds.compare_exchange_weak(
			m_reusableId->m_next,
			m_reusableId,
			std::memory_order_release,
			std::memory_order_relaxed
		));
	}

	void operator=(
		const reusable_consecutive_global_id&
	) = delete;

	reusable_consecutive_global_id& operator=(
		reusable_consecutive_global_id&& other
	)
	{
		std::swap(m_reusableId, other.m_reusableId);
	}

	const Value& get() const
	{
		return m_reusableId->m_value;
	}

	operator const Value&() const
	{
		return get();
	}

	const Value& operator*() const
	{
		return get();
	}

	const Value* operator->() const
	{
		return &get();
	}
};

}

using detail::reusable_consecutive_global_id;
using detail::reusable_consecutive_global_id_default_increment;

}