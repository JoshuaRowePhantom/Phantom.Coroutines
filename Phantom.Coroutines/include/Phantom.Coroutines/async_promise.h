#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/immovable_object.h"
#include "awaiter_wrapper.h"
#include "type_traits.h"
#else
import Phantom.Coroutines.awaiter_wrapper;
import Phantom.Coroutines.immovable_object;
import Phantom.Coroutines.type_traits;
#endif
#include "detail/storage_for.h"
#include "async_manual_reset_event.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    typename Value,
    is_template_instantiation<basic_async_manual_reset_event> Event
> class basic_async_promise;

template<
    typename Value,
    is_async_manual_reset_event_policy... Policy
> using async_promise = basic_async_promise<
    Value,
    async_manual_reset_event<Policy...>
>;

template<
    typename Value,
    is_template_instantiation<basic_async_manual_reset_event> Event
> class basic_async_promise
    :
    storage_for<Value>
{
    Event m_event;

    typedef awaiter_type<async_manual_reset_event<>> manual_reset_event_awaiter_type;

    struct awaiter_key {};

    class awaiter
        :
    public awaiter_wrapper<Event&>
    {
        basic_async_promise& m_promise;

    public:
        awaiter(
            basic_async_promise& promise,
            awaiter_key = {}
        ) :
            m_promise(promise),
            awaiter_wrapper<Event&>{ [&]() -> decltype(auto) { return (promise.basic_async_promise::m_event); } }
        {}

        Value& await_resume() const noexcept
        {
            return m_promise.basic_async_promise::as<Value>();
        }
    };

public:
    basic_async_promise()
    {}

    template<
        typename... Args
    > basic_async_promise(
        Args&&... args
    )
    {
        emplace(
            std::forward<Args>(args)...
        );
    }

    ~basic_async_promise()
    {
        if (m_event.is_set())
        {
            this->destroy<Value>();
        }
    }

    awaiter operator co_await(
        this auto& self
        ) noexcept
    {
        return awaiter{ self };
    }

    template<
        typename ... Args
    > Value& emplace(
        this auto& self,
        Args&&... args
    )
    {
        assert(!self.basic_async_promise::m_event.is_set());

        auto& result = self.basic_async_promise::storage_for::emplace<Value>(
            std::forward<Args>(args)...
        );

        self.basic_async_promise::m_event.set();

        return result;
    }
};
}

using detail::async_promise;

}