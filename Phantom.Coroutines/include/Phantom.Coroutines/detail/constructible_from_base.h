#ifndef PHANTOM_COROUTINES_INCLUDE_CONSTRUCTIBLE_FROM_BASE_H
#define PHANTOM_COROUTINES_INCLUDE_CONSTRUCTIBLE_FROM_BASE_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#endif

namespace Phantom::Coroutines::detail
{
// This class allows constructing a derived class from one of its base classes,
// essentially supporting "using base::base" for copy and move constructors.
// All the base class's constructors are inherited.
//
// For example:
//
//struct base
//{
//    base() {}
//    base(const base&) {}
//};
//
//struct derived1 : constructible_from_base<base>
//{
//    using derived1::constructible_from_base::constructible_from_base;
//};
//
//struct derived2 : constructible_from_base<base>
//{
//    using derived2::constructible_from_base::constructible_from_base;
//};
//
//int main()
//{
//    derived1 d1;
//    derived2 d2{ d1 };
//}
PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename T
>
struct constructible_from_base
    :
    public T
{
    using T::T;

    constructible_from_base(
        const T& other
    )
        requires std::constructible_from<T, const T&>
    : T(other)
    {
    }

    constructible_from_base(
        T& other
    )
        requires std::constructible_from<T, T&>
    : T(other)
    {
    }

    constructible_from_base(
        T&& other
    )
        requires std::constructible_from<T, T&&>
    : T(std::move(other))
    {
    }

    constructible_from_base(
        const T&& other
    )
        requires std::constructible_from<T, const T&&>
    : T(std::move(other))
    {
    }
};
}
#endif
