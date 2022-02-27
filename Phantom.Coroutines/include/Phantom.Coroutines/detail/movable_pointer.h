#pragma once

namespace Phantom::Coroutines
{
namespace detail
{

template<
	typename Value,
	typename Derived
> class movable_pointer
{
protected:
	Value* m_value;

protected:
	movable_pointer(
		Value* value
	) :
		m_value{ value }
	{}

	template<
		typename Other
	> movable_pointer(
		movable_pointer<Value, Other>&& other
	) :
		m_value{ other.m_value }
	{
		other.m_value = nullptr;
	}

	movable_pointer(
		movable_pointer&& other
	) :
		m_value{ other.m_value }
	{
		other.m_value = nullptr;
	}

	movable_pointer& operator=(
		movable_pointer&& other
		)
	{
		// Copy locally so that we invoke the destructor
		// of the moved-from instance before we return.
		Derived temp{ static_cast<Derived&&>(other) };
		std::swap(m_value, temp.m_value);
		return *this;
	}

	template<
		typename Other
	> movable_pointer& operator=(
		movable_pointer<Value, Other>&& other
		)
	{
		// Copy locally so that we invoke the destructor
		// of the moved-from instance before we return.
		Other temp{ static_cast<Other&&>(other) };
		std::swap(m_value, temp.m_value);
		return *this;
	}
};

}
}