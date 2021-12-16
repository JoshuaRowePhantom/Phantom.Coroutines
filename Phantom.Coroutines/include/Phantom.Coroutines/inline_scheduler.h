#pragma once

#include "scheduler.h"

namespace Phantom::Coroutines
{
namespace detail
{

class inline_scheduler
{
public:
	suspend_never operator co_await() noexcept 
	{ 
		return suspend_never{}; 
	}
};

static_assert(scheduler<inline_scheduler>);

}
}