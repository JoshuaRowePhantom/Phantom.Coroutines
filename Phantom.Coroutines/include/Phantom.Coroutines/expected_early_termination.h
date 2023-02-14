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
    static bool is_error_value(
        const auto& value
    )
    {
        if constexpr (is_template_instantiation<std::remove_cvref_t<decltype(value)>, std::unexpected>)
        {
            return true;
        }
        else if constexpr (is_template_instantiation<std::remove_cvref_t<decltype(value)>, std::expected>)
        {
            return !value;
        }
        else
        {
            return false;
        }
    }

    template<
        is_template_instantiation<std::expected> ErrorResult
    >
    static ErrorResult get_result_value(
        ErrorResult&& value
    )
    {
        return ErrorResult{ std::forward<decltype(value)>(value) };
    }

    template<
        is_template_instantiation<std::expected> Expected
    >
    static decltype(auto) get_success_value(
        Expected&& value
    )
    {
        return *value;
    }

    template<
        is_template_instantiation<std::expected> ErrorResult,
        typename Value,
        typename Error
    >
    static ErrorResult get_error_result(
        std::expected<Value, Error> expected
    )
    {
        return std::unexpected
        {
            std::forward<Error>(expected.error())
        };
    }

    template<
        is_template_instantiation<std::expected> ErrorResult,
        typename Error
    >
    static ErrorResult get_error_result(
        std::unexpected<Error> unexpected
    )
    {
        return unexpected;
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

        auto get_error_result() const
        {
            return std::unexpected
            {
                m_expected.error()
            };
        }

        decltype(auto) await_resume()
        {
            return get_success_value(
                std::forward<Expected>(m_expected));
        }
    };

public:
    template<
        is_template_instantiation<std::expected> Expected
    > auto await_transform(
        this auto& self,
        Expected&& expected
    )
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
