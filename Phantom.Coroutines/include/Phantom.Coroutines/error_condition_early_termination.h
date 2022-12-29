#pragma once

#include "early_termination_task.h"
#include <system_error>
#include <variant>

namespace Phantom::Coroutines
{
namespace detail
{

class error_condition_early_termination_await_transformer
    :
    public early_termination_transformer
{
//    class void_awaiter : early_termination_awaiter
//    {
//        std::error_condition m_errorCondition;
//
//        void_awaiter(
//            error_condition_early_termination_await_transformer& transformer,
//            std::error_condition errorCondition
//        ) :
//            basic_early_termination_awaiter<Promise>{ transformer }
//        {}
//
//    public:
//        bool await_ready() const noexcept
//        {
//            return !m_errorCondition;
//        }
//
//        auto await_suspend() noexcept
//        {
//            this->return_value(
//                early_termination_result{ m_errorCondition }
//            );
//            return this->resume();
//        }
//
//        void await_resume() const noexcept
//        {
//            // This method will only be called if m_errorCondition
//            // did not contain an error condition.
//        }
//    };
//
//    template<
//        typename Result
//    >
//    class typed_awaiter : basic_early_termination_transformed_awaiter<Promise>
//    {
//        template<
//            is_early_termination_promise Promise
//        >
//        friend class error_condition_early_termination;
//
//        std::variant<Result, std::error_condition>& m_result;
//
//        typed_awaiter(
//            error_condition_early_termination_await_transformer& transformer,
//            std::variant<Result, std::error_condition>& result
//        ) :
//            basic_early_termination_awaiter<Promise>{ transformer },
//            m_result{ std::move(result) }
//        {}
//
//    public:
//        bool await_ready() const noexcept
//        {
//            return m_result.index() == 0;
//        }
//
//        auto await_suspend() noexcept
//        {
//            this->return_value(
//                early_termination_result
//                { 
//                    std::get<std::error_condition>(m_result) 
//                }
//            );
//            return this->resume();
//        }
//
//        decltype(auto) await_resume() const noexcept
//        {
//            return m_result.get<0>();
//        }
//    };
//
//public:
//    void_awaiter await_transform(
//        std::error_condition errorCondition
//    )
//    {
//        return void_awaiter
//        {
//            *this,
//            errorCondition
//        };
//    }
//
//    template<
//        typename Result
//    > typed_awaiter<Result> await_transform(
//        std::variant<Result, std::error_condition>&& result
//    )
//    {
//        return typed_awaiter<Result>
//        {
//            *this,
//            result
//        };
//    }
};

}
}
