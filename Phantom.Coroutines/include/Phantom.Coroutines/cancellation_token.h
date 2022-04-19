#include "detail/immovable_object.h"
#include <concepts>
#include <functional>

namespace Phantom::Coroutines
{
namespace detail
{

class cancellation_source;
class cancellation_registration;

class cancellation_token
{
public:
	cancellation_token() noexcept
	{}

	cancellation_token(
		const cancellation_source& source
	) noexcept
	{}

	cancellation_token(
		const cancellation_token& other
	) noexcept : cancellation_token{}
	{
		*this = other;
	}

	cancellation_token(
		cancellation_token&& other
	) noexcept : cancellation_token{}
	{
		*this = std::move(other);
	}

	~cancellation_token() noexcept
	{}

	cancellation_token& operator=(
		const cancellation_token&
		) noexcept
	{
		return *this;
	}

	cancellation_token& operator=(
		cancellation_token&&
	) noexcept
	{
		return *this;
	}

	// Determine whether a cancellation token can be cancelled. 
	// This is false if there are no cancellation_source instances
	// still in existence for a given cancellation_token,
	// or if this instance has become disconnected from its cancellation_source
	// via std::move().
	// This method is TRUE for a cancelled cancellation_token.
	bool can_be_cancelled() const noexcept
	{}

	bool is_cancelled() const noexcept
	{}

	auto operator co_await () const noexcept
	{}
};

class cancellation_source
{
	friend class cancellation_token;

public:
	bool cancel() noexcept
	{
	}

	bool is_cancelled() const noexcept
	{
	}

	cancellation_token token() const noexcept
	{
	}
};

// Design notes:
// 
// There are a number of tradeoffs to make here:
// 1. Can the cancellation_registration be moved?
// 2. Should the lambda object be kept around even if the cancellation_token
//    cannot be cancelled?
// 
// Allowing the cancellation_registration to be moved opens the way
// for non-allocating passing of a cancellation registration from
// one place to another, but then requires that the identifying object
// for the cancellation_registration be other than the registration
// itself.  The lambda object would have to be stored
// in the cancellation_state, as the act of cancelling cannot reach out
// to a potentially movable cancellation_registration object.
//
// Keeping the lambda object around even if the cancellation_token
// cannot be cancelled means a few things:
//   1. The initial construction of a non-viable registration
//      will copy the lambda into an std::function object,
//      potentially allocating, even though the lambda will never be called.
//   2. If the lambda is stored in the cancellation state, then removing
//      it atomically might be problematic.
//   3. This allows for a design pattern where a caller can keep e.g. a shared_ptr
//      accessible via only the cancellation_registration.
//   4. A decision would need to be made on whether the lambda is destroyed
//      when the cancellation_source becomes cancelled, e.g. after the cancellation
//      occurs, or whether the lambda should exist until the cancellation_registration
//      itself is destroyed.
class cancellation_registration
	:
private immovable_object
{
	std::function<void()> m_callback;

public:
	template<
		std::invocable<> Lambda
	>
	cancellation_registration(
		const cancellation_token& cancellationToken,
		Lambda&& callback
	) noexcept(noexcept(m_callback = callback))
	{
		if (cancellationToken.can_be_cancelled())
		{
			m_callback = callback;
		}
	}

	~cancellation_registration() noexcept
	{}
};

}
using detail::cancellation_token;
using detail::cancellation_source;
using detail::cancellation_registration;
}
