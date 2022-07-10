export module Phantom.Coroutines.inline_scheduler;

import Phantom.Coroutines.scheduler;
import Phantom.Coroutines.coroutine;

namespace Phantom::Coroutines
{

export class inline_scheduler
{
public:
	suspend_never schedule() noexcept 
	{ 
		return suspend_never{}; 
	}
};

static_assert(is_scheduler<inline_scheduler>);

}

