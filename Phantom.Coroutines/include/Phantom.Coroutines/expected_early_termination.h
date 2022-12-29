#pragma once

#include "early_termination_task.h"
#include "type_traits.h"
#include <concepts>
#include <expected>
#include <utility>
#include <type_traits>

namespace Phantom::Coroutines
{
namespace detail
{

class expected_early_termination_result
    :
    public early_termination_result
{
public:
    template<
        is_template_instantiation<std::expected> Expected
    >
    static decltype(auto) return_result(
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

class expected_early_termination_transformer
    :
    public early_termination_transformer
{
    template<
        typename Promise,
        typename Expected
    >
    class expected_awaiter :
        public early_termination_synchronous_awaiter<Promise>,
        public expected_early_termination_result
    {
        Expected&& m_expected;

    public:
        expected_awaiter(
            Promise& promise,
            Expected&& expected
        ) noexcept :
            early_termination_synchronous_awaiter<Promise>{ promise },
            m_expected{ std::forward<Expected>(expected) }
        {}

        bool is_error() const noexcept
        {
            return !m_expected.has_value();
        }

        auto return_value() const
        {
            return std::unexpected
            {
                m_expected.error()
            };
        }

        decltype(auto) await_resume()
        {
            return return_result(
                std::forward<Expected>(m_expected));
        }
    };

public:
    template<
        typename Expected
    > auto await_transform(
        this auto& self,
        Expected&& expected
    ) requires is_template_instantiation<Expected, std::expected>
    {
        return expected_awaiter
        {
            self,
            std::forward<Expected>(expected)
        };
    }
};

}

using detail::expected_early_termination_result;
using detail::expected_early_termination_transformer;

}
