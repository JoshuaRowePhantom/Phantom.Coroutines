#ifndef PHANTOM_COROUTINES_INCLUDE_CORO_OPERATION_CANCELLED_HPP
#define PHANTOM_COROUTINES_INCLUDE_CORO_OPERATION_CANCELLED_HPP

#include<exception>

namespace cppcoro
{

class operation_cancelled : public std::exception
{
public:

    operation_cancelled() noexcept
        : std::exception()
    {}

    const char* what() const noexcept override { return "operation cancelled"; }
};

}
#endif
