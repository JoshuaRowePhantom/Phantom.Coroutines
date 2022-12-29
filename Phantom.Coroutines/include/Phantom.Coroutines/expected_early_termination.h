#pragma once

#include "early_termination_task.h"
#include "type_traits.h"
#include <concepts>
#include <utility>
#include <type_traits>

namespace Phantom::Coroutines
{
namespace detail
{

class expected_early_termination_transformer
    :
    public early_termination_transformer
{
public:

};

class expected_early_termination_result
    :
    public early_termination_result
{
public:
    template<
        is_template_instantiation<std::expected> Expected
    >
    decltype(auto) return_result(
        Expected&& expected
    )
    {
        if constexpr (std::same_as<void, typename Expected::value_type>)
        {
            return;
        }
        else if constexpr (std::is_lvalue_reference_v<typename Expected::value_type>)
        {
            return *expected;
        }
        else
        {
            return std::forward_like<Expected>(
                *expected);
        }
    }
};

}

using detail::expected_early_termination_result;
using detail::expected_early_termination_transformer;

}
