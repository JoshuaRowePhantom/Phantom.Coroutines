#pragma once

#include "detail/coroutine.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "await_none_await_transform.h"
#include "extensible_promise.h"
#include <concepts>
#include <exception>
#include <variant>
#include <type_traits>


namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename Promise
> class basic_async_generator;

template<
    typename Promise
> class async_generator_yield_awaiter
    :
    public extensible_awaitable<Promise>
{
public:
    using typename extensible_awaitable<Promise>::promise_type;
    using typename extensible_awaitable<Promise>::coroutine_handle_type;

    using extensible_awaitable<Promise>::extensible_awaitable;

    bool await_ready() const noexcept { return false; }

    std::coroutine_handle<> await_suspend(
        this auto& self,
        std::coroutine_handle<>
    )
    {
        return self.promise().m_continuation;
    }

    void await_resume() const noexcept {}
};

template<
    typename Result
> class basic_async_generator_promise
{
public:
    using result_type = Result;

private:
    template<
        typename Promise
    > friend class async_generator_iterator;

    template<
        typename Promise
    > friend class async_generator_increment_awaiter;

    template<
        typename Promise
    > friend class async_generator_yield_awaiter;
    
    template<
        typename Promise
    > friend class basic_async_generator;

    typedef std::variant<
        std::monostate,
        std::reference_wrapper<std::remove_reference_t<result_type>>,
        std::remove_cvref_t<result_type>,
        std::exception_ptr,
        std::monostate
    > current_value_holder_type;

    // The iterator needs to be advanced.
    static const std::size_t EmptyIndex = 0;
    // The iterator holds a reference to a value.
    static const std::size_t ValueRefIndex = 1;
    // The iterator holds a copy of a value.
    static const std::size_t ValueIndex = 2;
    // The iterator holds an exception.
    static const std::size_t ExceptionIndex = 3;
    // The iterator is complete.
    static const std::size_t CompleteIndex = 4;

    current_value_holder_type m_currentValue;
    coroutine_handle<> m_continuation;

public:
    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return basic_async_generator{ self };
    }

    suspend_always initial_suspend(
        this auto& self
    ) noexcept
    {
        return suspend_always{};
    }

    template<
        typename Value
    > auto yield_value(
        this auto&& self,
        Value&& value
    )
    {
        if constexpr (
            std::same_as<std::remove_reference_t<result_type>, std::remove_reference_t<Value>>
            &&
            (
                std::is_reference_v<result_type>
                || std::is_rvalue_reference_v<Value&&>
            ))
        {
            self.m_currentValue.emplace<ValueRefIndex>(
                static_cast<std::add_lvalue_reference_t<result_type>>(
                    value));
        }
        else
        {
            self.m_currentValue.emplace<ValueIndex>(
                std::forward<Value>(value));
        }

        return async_generator_yield_awaiter{ self };
    }

    void return_void(
        this auto& self
    )
    {
        self.m_currentValue.emplace<CompleteIndex>();
    }

    void unhandled_exception(
        this auto& self
    )
    {
        self.m_currentValue.emplace<ExceptionIndex>(
            std::current_exception());
    }

    final_suspend_transfer final_suspend(
        this auto& self
    ) noexcept
    {
        return final_suspend_transfer
        {
            self.m_continuation
        };
    }
};

template<
    typename Promise
> class async_generator_increment_awaiter
    :
public extensible_awaitable<Promise>
{
    using promise_type = Promise;

public:
    using extensible_awaitable<Promise>::extensible_awaitable;

    bool await_ready(
        this auto& self
    ) noexcept 
    {
        return !self || self.promise().m_currentValue.index() != promise_type::EmptyIndex;
    }

    auto await_suspend(
        this auto& self,
        auto continuation
    ) noexcept
    {
        self.promise().m_continuation = continuation;
        return self.handle();
    }

    auto await_resume(
        this auto& self)
    {
        if (self && self.promise().m_currentValue.index() == promise_type::ExceptionIndex)
        {
            std::rethrow_exception(
                std::get<promise_type::ExceptionIndex>(
                    self.promise().m_currentValue));
        }

        return async_generator_iterator{ self.handle() };
    }
};

template<
    typename Promise
> class async_generator_iterator
    :
    public extensible_awaitable<Promise>
{
    using promise_type = Promise;
    using result_type = typename promise_type::result_type;

    promise_type* m_promise;

public:
    typedef std::remove_reference_t<result_type> value_type;
    typedef size_t difference_type;
    typedef std::add_lvalue_reference_t<result_type> reference;
    typedef std::input_iterator_tag iterator_category;

    using extensible_awaitable<Promise>::extensible_awaitable;

    auto operator++(
        this auto& self)
    {
        self.promise().m_currentValue.emplace<promise_type::EmptyIndex>();
        return async_generator_increment_awaiter{ self.promise() };
    }

    std::add_lvalue_reference_t<result_type> operator*()
    {
        if (this->promise().m_currentValue.index() == promise_type::ValueIndex)
        {
            return std::get<promise_type::ValueIndex>(
                this->promise().m_currentValue);
        }

        return std::get<promise_type::ValueRefIndex>(
            this->promise().m_currentValue);
    }

    std::remove_reference_t<result_type>* operator->(
        this auto& self)
    {
        return &*self;
    }

    explicit operator bool(
        this auto& self
        ) 
    {
        return self.handle()
            && self.promise().m_currentValue.index() != promise_type::CompleteIndex;
    }

    bool operator==(
        const async_generator_iterator& other
        )
        const
    {
        return this->handle() == other.handle()
            || !*this && !other;
    }

    bool operator!=(
        const async_generator_iterator& other
        )
        const
    {
        return !(*this == other);
    }
};

template<
    typename Promise
> class basic_async_generator
    :
    public extensible_awaitable<Promise>
{
public:
    using promise_type = Promise;
    using result_type = typename promise_type::result_type;
    using iterator_type = async_generator_iterator<Promise>;

public:
    using extensible_awaitable<Promise>::extensible_awaitable;

    basic_async_generator(
        const basic_async_generator&
    ) = delete;

    basic_async_generator(
        basic_async_generator&& other
    ) :
        extensible_awaitable<Promise>{ other.handle() }
    {
        other.handle() = nullptr;
    }

    void operator=(
        const basic_async_generator&
        ) = delete;

    basic_async_generator& operator=(
        this auto& self,
        basic_async_generator&& other
        )
    {
        auto temp = std::move(self);
        std::swap(self.handle(), other.handle());
        return self;
    }

    ~basic_async_generator()
    {
        if (this->handle())
        {
            this->handle().destroy();
        }
    }

    auto begin(
        this auto& self
    )
    {
        return async_generator_increment_awaiter { self.handle() };
    }

    auto end(
    )
    { 
        return async_generator_iterator<Promise>{};
    }
};

template<
    typename Promise
> basic_async_generator(Promise&) -> basic_async_generator<Promise>;

template<
    typename Result
> using async_generator_promise = basic_async_generator_promise<
    Result
>;

template<
    typename Result
> using async_generator = basic_async_generator<
    async_generator_promise<Result>
>;

}

using detail::basic_async_generator;
using detail::basic_async_generator_promise;
using detail::async_generator;

}
