#pragma once

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