export module Phantom.Coroutines.assert_same_thread;

#if NDEBUG
#else
import <assert.h>;
import <thread>;
#endif

namespace Phantom::Coroutines
{

#if NDEBUG
export class assert_same_thread
{
public:
	assert_same_thread()
	{
	}

	void check_thread() const
	{
	}

	~assert_same_thread()
	{
	}
};
#else
export class assert_same_thread
{
	std::thread::id m_threadId;
public:
	assert_same_thread()
		:
		m_threadId{ std::this_thread::get_id() }
	{
	}

	void check_thread() const
	{
		assert(m_threadId == std::this_thread::get_id());
	}

	~assert_same_thread()
	{
		check_thread();
	}
};
#endif

}