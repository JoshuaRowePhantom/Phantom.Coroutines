#include <functional>
#include <optional>
#include <stop_token>
#include "async_mutex.h"
#include "async_scope.h"
#include "detail/movable_pointer.h"
#include "shared_task.h"
#include "single_consumer_auto_reset_event.h"
#include "sync_wait.h"
#include "task.h"

namespace Phantom::Coroutines
{
namespace detail
{

class processor_pool
{
	class friend_key {};
public:
	class exit_token;
	class processor_token;

	typedef unsigned int processor_count_type;
	typedef std::function<
		task<exit_token>(
			processor_token
			)
	> processor_generator_type;

	class [[nodiscard]] exit_token :
		public movable_pointer<processor_pool, exit_token>
	{
	public:
		exit_token(
			processor_pool* processorPool,
			friend_key = {})
			:
			movable_pointer{ processorPool }
		{
		}

		exit_token(
			exit_token&&
		) = default;

		exit_token& operator=(
			exit_token&&
		) = default;

		processor_pool* claim(
			friend_key = {})
		{
			auto result = m_value;
			m_value = nullptr;
			return result;
		}

		operator bool() const
		{
			return m_value;
		}

		~exit_token()
		{
			if (m_value)
			{
				m_value->m_currentProcessorCount.fetch_add(1, std::memory_order_relaxed);
				m_value->m_processorCountsChanged_Generator.set();
				m_value->m_processorCountsChanged_Modifier.set();
			}
		}
	};
	
	class [[nodiscard]] processor_token :
		public movable_pointer<processor_pool, processor_token>
	{
	public:
		processor_token(
			processor_pool& processorPool,
			friend_key = {}
		) :
			movable_pointer{ &processorPool }
		{
			m_value->m_currentProcessorCount.fetch_add(1, std::memory_order_relaxed);
			m_value->m_processorCountsChanged_Generator.set();
			m_value->m_processorCountsChanged_Modifier.set();
		}

		exit_token acquire_exit_token_if_necessary()
		{
			bool needExit = false;

			processor_count_type targetProcessorCount = m_value->m_targetProcessorCount.load(std::memory_order_acquire);
			processor_count_type currentProcessorCount = m_value->m_currentProcessorCount.load(std::memory_order_acquire);

			while (
				targetProcessorCount < currentProcessorCount
				&&
				!(needExit = m_value->m_currentProcessorCount.compare_exchange_weak(
					currentProcessorCount,
					currentProcessorCount - 1,
					std::memory_order_release,
					std::memory_order_acquire))
				)
			{
				targetProcessorCount = m_value->m_targetProcessorCount.load(std::memory_order_relaxed);
			}

			if (needExit)
			{
				return exit_token{ m_value };
			}

			return { nullptr };
		}

		~processor_token()
		{
			if (m_value)
			{
				m_value->m_currentProcessorCount.fetch_sub(1, std::memory_order_release);
				m_value->m_processorCountsChanged_Generator.set();
				m_value->m_processorCountsChanged_Modifier.set();
			}
		}
	};

private:
	async_mutex m_targetProcessorCountMutex;
	single_consumer_auto_reset_event m_processorCountsChanged_Generator;
	single_consumer_auto_reset_event m_processorCountsChanged_Modifier;
	std::atomic<processor_count_type> m_targetProcessorCount;
	std::atomic<processor_count_type> m_currentProcessorCount;
	std::future<void> m_generateProcessorsFuture;
	async_scope m_processorTasks;
	std::stop_source m_stopSource;

	shared_task<> RunOneProcessor(
		task<exit_token> processor
	)
	{
		auto exitToken{ co_await std::move(processor) };
		assert(exitToken.claim() == this);
	}

	task<> generate_processors(
		processor_generator_type processorGenerator
	)
	{
		while (!m_stopSource.stop_requested())
		{
			while (m_targetProcessorCount.load(std::memory_order_acquire) < m_currentProcessorCount.load(std::memory_order_acquire))
			{
				m_processorTasks.spawn(
					RunOneProcessor(
						std::move(
							processorGenerator(
								processor_token{ *this })
				)));
			}

			co_await m_processorCountsChanged_Generator;
		}

		co_await m_processorTasks.join();
	}

public:

	processor_pool(
		processor_generator_type processorGenerator,
		processor_count_type processorCount = 0
	)
	{
		m_generateProcessorsFuture = as_future(
			generate_processors(
				std::move(processorGenerator)));

		sync_wait(
			set_target_processor_count(processorCount)
		);
	}

	~processor_pool()
	{
		m_stopSource.request_stop();

		sync_wait(
			set_target_processor_count(0)
		);

		m_generateProcessorsFuture.get();
	}

	task<> set_target_processor_count(
		processor_count_type threadCount
	)
	{
		auto lock{ co_await m_targetProcessorCountMutex.scoped_lock() };
		m_targetProcessorCount.store(threadCount, std::memory_order_relaxed);
		m_processorCountsChanged_Generator.set();

		while (m_currentProcessorCount.load(std::memory_order_acquire) != threadCount)
		{
			co_await m_processorCountsChanged_Modifier;
		}
	}

	processor_count_type get_target_thread_count() const
	{
		return m_targetProcessorCount.load(std::memory_order_acquire);
	}
};

}
}
