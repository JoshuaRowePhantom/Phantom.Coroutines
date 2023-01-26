#pragma once

#include "awaiter_wrapper.h"
#include "extensible_promise.h"
#include "task.h"
#include <concepts>
#include <exception>
#include <variant>
#include <type_traits>


namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename T
> concept is_async_generator_policy =
is_base_promise_type_policy<T>;

template<
    typename Promise
> class basic_async_generator;

template<
    typename Promise
> class async_generator_yield_awaiter
    :
    public extensible_promise_handle<Promise>
{
public:
    using typename extensible_promise_handle<Promise>::promise_type;
    using typename extensible_promise_handle<Promise>::coroutine_handle_type;

    using extensible_promise_handle<Promise>::extensible_promise_handle;

    bool await_ready() const noexcept 
    {
        return false; 
    }

    std::coroutine_handle<> await_suspend(
        this auto& self,
        std::coroutine_handle<>
    )
    {
        return self.promise().continuation();
    }

    void await_resume() const noexcept 
    {
    }
};

struct async_generator_current_value_index
{
    // The iterator needs to be advanced,
    // or the underlying coroutine has completed.
    static const std::size_t EmptyIndex = 0;
    // The iterator holds a reference to a value.
    static const std::size_t ValueRefIndex = 1;
    // The iterator holds a copy of a value.
    static const std::size_t ValueIndex = 2;
};

template<
    typename Result,
    typename BasePromise
> class basic_async_generator_promise
    :
    public derived_promise<BasePromise>,
    private async_generator_current_value_index
{
public:
    using value_type = Result;
    using async_generator_base_promise_type = BasePromise;

private:
    template<
        is_derived_instantiation<basic_async_generator> Generator
    > friend class async_generator_iterator;

    template<
        is_derived_instantiation<basic_async_generator> Generator
    > friend class async_generator_increment_awaiter;

    template<
        typename Promise
    > friend class async_generator_yield_awaiter;
    
    template<
        typename Promise
    > friend class basic_async_generator;

    typedef std::variant<
        std::monostate,
        std::reference_wrapper<std::remove_reference_t<value_type>>,
        std::remove_cvref_t<value_type>,
        std::exception_ptr,
        std::monostate
    > current_value_holder_type;

    current_value_holder_type m_currentValue;

public:
    template<
        typename Self
    > auto get_return_object(
        this Self& self
    ) noexcept
    {
        return basic_async_generator<Self>
        {
            [&]() { return self.derived_promise<BasePromise>::get_return_object(); }
        };
    }

    template<
        typename Value
    > auto yield_value(
        this auto&& self,
        Value&& value
    )
    {
        if constexpr (
            std::same_as<std::remove_reference_t<value_type>, std::remove_reference_t<Value>>
            &&
            (
                std::is_reference_v<value_type>
                || std::is_rvalue_reference_v<Value&&>
            ))
        {
            self.m_currentValue.emplace<ValueRefIndex>(
                static_cast<std::add_lvalue_reference_t<value_type>>(
                    value));
        }
        else
        {
            self.m_currentValue.emplace<ValueIndex>(
                std::forward<Value>(value));
        }

        return async_generator_yield_awaiter{ self };
    }
};

template<
    is_derived_instantiation<basic_async_generator> Generator
> class async_generator_increment_awaiter
    :
private async_generator_current_value_index
{
    template<
        is_derived_instantiation<basic_async_generator> Generator
    > friend class async_generator_begin_awaiter;

    using promise_type = typename Generator::promise_type;

    Generator& m_generator;

    decltype(auto) promise(
        this auto& self
    )
    {
        return self.m_generator.promise();
    }

    decltype(auto) currentValue(
        this auto& self
    )
    {
        return (self.promise().m_currentValue);
    }

    decltype(auto) awaiter(
        this auto& self
    )
    {
        return self.m_generator.awaiter();
    }

public:
    async_generator_increment_awaiter(
        Generator& generator
    ) : m_generator{generator}
    {}

    auto await_ready(
        this auto& self,
        auto&&... args
    )
    {
        return self.awaiter().await_ready(
            std::forward<decltype(args)>(args)...
        );
    }

    auto await_suspend(
        this auto& self,
        auto continuation,
        auto&&... args)
    {
        self.currentValue().emplace<EmptyIndex>();

        return self.awaiter().await_suspend(
            continuation,
            std::forward<decltype(args)>(args)...
        );
    }

    auto await_resume(
        this auto& self
        )
    {
        if (self.currentValue().index() == ValueRefIndex
            || self.currentValue().index() == ValueIndex)
        {
            return self.awaiter().get_result_value(
                [&]() { return async_generator_iterator<Generator>{ &self.m_generator }; }
            );
        }

        scope_guard clearGenerator = [&]
        {
            self.m_generator.handle() = nullptr;
        };

        return self.awaiter().await_resume_value(
            [] { return async_generator_iterator<Generator>{}; }
        );
    }
};


template<
    is_derived_instantiation<basic_async_generator> Generator
> class async_generator_begin_awaiter
    :
    public async_generator_increment_awaiter<Generator>
{
    using async_generator_begin_awaiter::async_generator_begin_awaiter::async_generator_begin_awaiter;
};

template<
    typename Generator
> async_generator_begin_awaiter(Generator&) -> async_generator_begin_awaiter<Generator>;

template<
    is_derived_instantiation<basic_async_generator> Generator
> class async_generator_iterator
    :
    private async_generator_current_value_index
{
    friend class async_generator_increment_awaiter<Generator>;
    friend class basic_async_generator<typename Generator::promise_type>;

    using promise_type = typename Generator::promise_type;
    Generator* m_generator;

    async_generator_iterator(
        Generator* generator
    ) :
        m_generator{ generator }
    {}

    auto& promise(
        this auto& self)
    {
        return self.m_generator->promise();
    }

public:
    async_generator_iterator(
    ) :
        m_generator{nullptr}
    {}

    using value_type = typename promise_type::value_type;
    typedef size_t difference_type;
    typedef std::add_lvalue_reference_t<value_type> reference;
    typedef std::input_iterator_tag iterator_category;

    auto operator++(
        this auto& self)
    {
        self.promise().m_currentValue.emplace<EmptyIndex>();
        return async_generator_increment_awaiter
        { 
            *self.m_generator,
        };
    }

    reference operator*()
    {
        if (promise().m_currentValue.index() == ValueIndex)
        {
            return std::get<ValueIndex>(
                promise().m_currentValue);
        }

        return std::get<ValueRefIndex>(
            promise().m_currentValue);
    }

    std::remove_reference_t<value_type>* operator->(
        this auto& self)
    {
        return &*self;
    }

    explicit operator bool(
        this auto& self
        ) 
    {
        return self.m_generator
            && self.m_generator->handle()
            && self.promise().m_currentValue.index() != EmptyIndex;
    }

    auto operator ==(
        const async_generator_iterator& other
        ) const
    {
        return m_generator == other.m_generator
            || !*this && !other;
    }

    auto operator !=(
        const async_generator_iterator& other
        ) const
    {
        return !(*this == other);
    }
};

decltype(auto) get_async_generator_base_return_object(
    auto& promise
)
{
    return promise.async_generator_base_promise_type::get_return_object();
}

template<
    typename Promise
> class basic_async_generator
    :
    public extended_promise_handle<awaiter_wrapper<decltype(get_async_generator_base_return_object(std::declval<Promise&>()))>>
{
    friend class async_generator_increment_awaiter<basic_async_generator>;
    friend class async_generator_iterator<basic_async_generator>;
    
    using awaiter_wrapper_type = typename basic_async_generator::extended_promise_handle::promise_handle_type;
    using awaitable_type = typename awaiter_wrapper_type::awaiter_type;

protected:
    decltype(auto) awaiter(
        this auto& self
    )
    {
        return self.basic_async_generator::extended_promise_handle::awaitable().awaiter();
    }

public:
    using typename basic_async_generator::extended_promise_handle::promise_type;
    using result_type = typename promise_type::result_type;
    using value_type = typename promise_type::value_type;
    using iterator_type = async_generator_iterator<basic_async_generator>;

public:
    basic_async_generator()
    {}

    basic_async_generator(
        std::invocable auto&& awaitableFunction
    ) :
        basic_async_generator::extended_promise_handle
    {
        [&]()
        {
            return awaiter_wrapper_type{ std::forward<decltype(awaitableFunction)>(awaitableFunction) };
        }
    }
    {}

    auto begin()
    {
        return async_generator_begin_awaiter{ *this };
    }

    auto end()
    {
        return iterator_type{};
    }
};

template<
    typename Result,
    typename ... Policies
> using async_generator_promise = basic_async_generator_promise<
    Result,
    select_base_promise_type<Policies..., base_promise_type<task_promise<void>>>
>;

template<
    typename Result,
    typename ... Policies
> using async_generator = basic_async_generator<
    async_generator_promise<
        Result,
        Policies...
    >
>;

}

using detail::basic_async_generator;
using detail::basic_async_generator_promise;
using detail::async_generator;

}
