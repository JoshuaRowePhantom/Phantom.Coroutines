#include "Phantom.Coroutines/inline_scheduler.h"
namespace cppcoro
{
class inline_scheduler
{
	Phantom::Coroutines::inline_scheduler m_scheduler;
public:
	auto schedule()
	{
		return m_scheduler.operator co_await();
	}
};
}