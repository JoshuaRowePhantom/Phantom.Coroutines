#ifndef PHANTOM_COROUTINES_INCLUDE_GENERATOR_H
#define PHANTOM_COROUTINES_INCLUDE_GENERATOR_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include <concepts>
#include <exception>
#include <iterator>
#include <variant>
#include <type_traits>
#include "Phantom.Coroutines/detail/coroutine.h"
#include "detail/immovable_object.h"
#endif

static_assert(PHANTOM_COROUTINES_IS_CONFIGURED);
PHANTOM_COROUTINES_ASSERT_IS_MODULE;

namespace Phantom::Coroutines
{
namespace detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Traits
> concept GeneratorTraits = requires
{
    typename Traits::generator_type;
    typename Traits::iterator_type;
    typename Traits::promise_type;
    typename Traits::result_type;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    GeneratorTraits Traits
> class basic_generator;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    GeneratorTraits Traits
> class basic_generator_promise
{
    template<
        GeneratorTraits
    > friend class basic_generator_iterator;

    template<
        GeneratorTraits
    > friend class basic_generator;

    using promise_type = typename Traits::promise_type;
    using result_type = typename Traits::result_type;
    using generator_type = typename Traits::generator_type;

    typedef std::variant<
        std::monostate,
        std::reference_wrapper<std::remove_reference_t<result_type>>,
        std::remove_cvref_t<result_type>,
        std::exception_ptr
    > current_value_holder_type;

    static const std::size_t EmptyIndex = 0;
    static const std::size_t ValueRefIndex = 1;
    static const std::size_t ValueIndex = 2;
    static const std::size_t ExceptionIndex = 3;

    current_value_holder_type m_currentValue;

public:
    generator_type get_return_object()
    {
        return generator_type{ static_cast<promise_type&>(*this) };
    }

    suspend_never initial_suspend() noexcept
    {
        return suspend_never{};
    }

    template<
        typename Value
    > suspend_always yield_value(
        Value&& value
    )
    {
        m_currentValue.template emplace<ValueIndex>(
            std::forward<Value>(value));
        return suspend_always{};
    }

    suspend_always yield_value(
        result_type& value
    )
        requires std::is_reference_v<result_type>
    {
        m_currentValue.template emplace<ValueRefIndex>(
            static_cast<std::add_lvalue_reference_t<result_type>>(
                value));
        return suspend_always{};
    }

    suspend_always yield_value(
        std::remove_reference_t<result_type>&& value
    )
    {
        m_currentValue.template emplace<ValueRefIndex>(
            static_cast<std::add_lvalue_reference_t<result_type>>(
                value));
        return suspend_always{};
    }

    template<
        typename T
    > void await_transform(
        T&&
    ) = delete;

    void return_void()
    {
        m_currentValue.template emplace<EmptyIndex>();
    }

    void unhandled_exception()
    {
        m_currentValue.template emplace<ExceptionIndex>(
            std::current_exception());
    }

    suspend_always final_suspend() noexcept
    {
        return suspend_always{};
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    GeneratorTraits Traits
> class basic_generator_iterator
{
    using promise_type = typename Traits::promise_type;
    using generator_type = typename Traits::generator_type;
    using result_type = typename Traits::result_type;
    using basic_promise_type = basic_generator_promise<Traits>;

    promise_type* m_promise;

public:
    typedef std::remove_reference_t<result_type> value_type;
    typedef size_t difference_type;
    typedef std::add_lvalue_reference_t<result_type> reference;
    typedef std::input_iterator_tag iterator_category;

    basic_generator_iterator()
        :
        m_promise{ nullptr }
    {}

    basic_generator_iterator(
        generator_type& generator
    ) :
        m_promise { generator.m_promise }
    {
        if (m_promise->m_currentValue.index() == basic_promise_type::EmptyIndex)
        {
            m_promise = nullptr;
        }
    }

    basic_generator_iterator& operator++()
    {
        coroutine_handle<promise_type>::from_promise(*m_promise).resume();

        if (m_promise->m_currentValue.index() == basic_promise_type::ExceptionIndex)
        {
            std::rethrow_exception(
                std::get<basic_promise_type::ExceptionIndex>(
                    m_promise->m_currentValue));
        }
        
        if (m_promise->m_currentValue.index() == basic_promise_type::EmptyIndex)
        {
            m_promise = nullptr;
        }

        return *this;
    }

    std::add_lvalue_reference_t<result_type> operator*()
    {
        if (m_promise->m_currentValue.index() == basic_promise_type::ValueIndex)
        {
            return std::get<basic_promise_type::ValueIndex>(
                m_promise->m_currentValue);
        }

        return std::get<basic_promise_type::ValueRefIndex>(
            m_promise->m_currentValue);
    }

    std::remove_reference_t<result_type>* operator->()
    {
        return &*this;
    }

    bool operator==(
        const basic_generator_iterator& other
        )
        const
    {
        return m_promise == other.m_promise;
    }

    bool operator!=(
        const basic_generator_iterator& other
        )
        const
    {
        return m_promise != other.m_promise;
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    GeneratorTraits Traits
> class basic_generator
{
    template<
        GeneratorTraits
    > friend class basic_generator_iterator;
    
    using basic_promise_type = basic_generator_promise<Traits>;

public:
    using promise_type = typename Traits::promise_type;
    using generator_type = typename Traits::generator_type;
    using iterator_type = typename Traits::iterator_type;

private:
    promise_type* m_promise;

public:
    basic_generator()
        : 
        m_promise { nullptr }
    {}

    basic_generator(
        promise_type& promise
    ) :
        m_promise
    {
        &promise
    }
    {}

    basic_generator(
        const basic_generator&
    ) = delete;

    basic_generator(
        basic_generator&& other
    ) :
        m_promise{ other.m_promise }
    {
        other.m_promise = nullptr;
    }

    void operator=(
        const basic_generator&
        ) = delete;

    basic_generator& operator=(
        basic_generator&& other
        )
    {
        std::swap(m_promise, other.m_promise);
        return *this;
    }

    ~basic_generator() 
    {
        if (m_promise)
        {
            coroutine_handle<promise_type>::from_promise(*m_promise).destroy();
        }
    }

    iterator_type begin()
    {
        if (m_promise == nullptr)
        {
            return iterator_type{};
        }

        if (m_promise->m_currentValue.index() == basic_promise_type::ExceptionIndex)
        {
            std::rethrow_exception(
                std::get<basic_promise_type::ExceptionIndex>(
                    m_promise->m_currentValue));
        }

        return iterator_type{ static_cast<generator_type&>(*this) };
    }

    iterator_type end() const 
    { 
        return iterator_type{};
    }
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
> class generator;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
> class generator_promise;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
> class generator_iterator;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
> struct generator_traits
{
    typedef generator<TResult> generator_type;
    typedef generator_promise<TResult> promise_type;
    typedef generator_iterator<TResult> iterator_type;
    typedef TResult result_type;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename TResult
> class generator
    :
public basic_generator<
    generator_traits<TResult>
>
{};

template<
    typename TResult
> class generator_promise
    :
public basic_generator_promise<
    generator_traits<TResult>
>
{};

template<
    typename TResult
> class generator_iterator
    :
public basic_generator_iterator<
    generator_traits<TResult>
>
{
public:
    using generator_iterator::basic_generator_iterator::basic_generator_iterator;
};

}

PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_generator;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_generator_iterator;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::basic_generator_promise;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::generator;
PHANTOM_COROUTINES_MODULE_EXPORT
using detail::GeneratorTraits;

}
#endif
