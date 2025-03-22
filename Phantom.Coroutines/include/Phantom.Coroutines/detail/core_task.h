#ifndef PHANTOM_COROUTINES_INCLUDE_CORE_TASK_H
#define PHANTOM_COROUTINES_INCLUDE_CORE_TASK_H
#ifndef PHANTOM_COROUTINES_COMPILING_MODULES
#include "detail/variant_result_storage.h"
#include <concepts>
#include <exception>
#include <type_traits>
#include <variant>
#include "detail/coroutine.h"
#include "extensible_promise.h"
#include "detail/final_suspend_transfer.h"
#include "detail/immovable_object.h"
#include "detail/non_copyable.h"
#include "policies.h"
#include "type_traits.h"
#endif

#include "assert_is_configured_module.h"

namespace Phantom::Coroutines::detail
{

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result,
    is_continuation Continuation,
    template<typename Result> typename PromiseBase
> class core_task_promise;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class core_task;

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Promise
> class core_task_awaiter;

template<
    typename Result
>
class core_task_variant_return_result
{
public:

    void return_variant_result(
        this auto& self,
        Result value
    ) requires !std::same_as<void, Result>
    {
        self.m_result.emplace<self.result_index>(std::move(value));
    }

    void return_variant_result(
        this auto& self,
        const Result& value
    )
    {
        self.m_result.emplace<self.result_index>(value);
    }
};

template<
>
class core_task_variant_return_result<void>
{
public:
};

template<
    typename Result
>
class core_task_variant_result
    :
    public variant_result_storage<Result>,
    public core_task_variant_return_result<Result>
{
public:
    using result_variant_type = std::variant<
        std::monostate,
        typename variant_result_storage<Result>::result_variant_member_type,
        std::exception_ptr
    >;

    static constexpr size_t result_index = 1;
    static constexpr size_t exception_index = 2;

    result_variant_type m_result;

    void unhandled_exception()
    {
        m_result.emplace<exception_index>(
            std::current_exception());
    }

    void return_exception(
        std::exception_ptr exception)
    {
        m_result.emplace<exception_index>(
            exception);
    }

    void return_variant_result(
        auto&& value
    )
    {
        m_result.emplace<result_index>(
            std::forward<decltype(value)>(value));
    }

    bool has_exception(
    ) const noexcept
    {
        return m_result.index() == exception_index;
    }

    [[noreturn]]
    void resume_exception(
    )
    {
        std::rethrow_exception(
            get<exception_index>(
                m_result)
        );
    }

    decltype(auto) resume_value(
        this auto&& self)
    {
        return self.resume_variant_result<result_index>(
            std::forward<decltype(self)>(self).m_result);
    }

    decltype(auto) await_resume_value(
        this auto&& self,
        std::invocable auto&& valueFunction)
    {
        if (self.has_exception())
        {
            self.resume_exception();
        }

        return std::forward<decltype(valueFunction)>(valueFunction)();
    }

    decltype(auto) result(this auto&& self)
    {
        return std::forward<decltype(self)>(self);
    }

    decltype(auto) await_resume(
        this auto&& self)
    {
        return self.await_resume_value(
            [&]() -> decltype(auto)
        {
            return std::forward<decltype(self)>(self).resume_value();
        });
    }
};

template<
    typename Promise
>
class core_task_awaiter_result_base;

template<
    typename Promise
> 
requires Promise::is_reusable
class core_task_awaiter_result_base<
    Promise
>
    :
    public extensible_promise_handle<Promise>
{
protected:
    decltype(auto) result(
        this auto&& self)
    {
        return std::forward_like<decltype(self)>(self.promise());
    }

    void set_promise_variant_result_pointer()
    {}

    decltype(auto) await_resume(
        this auto&& self)
    {
        return std::forward<decltype(self)>(self).result().await_resume();
    }

    using core_task_awaiter_result_base::extensible_promise_handle::extensible_promise_handle;
};

template<
    typename Promise
>
    requires !Promise::is_reusable
class core_task_awaiter_result_base<
    Promise
>
    :
    public core_task_variant_result<typename Promise::result_type>,
    public single_owner_promise_handle<Promise>
{
protected:

    void set_promise_variant_result_pointer(
        this auto& self)
    {
        self.promise().Promise::core_non_reusable_task_promise_base::m_result = &self;
    }

    decltype(auto) await_resume(
        this auto&& self)
        requires std::is_rvalue_reference_v<decltype(self)>
    {
        auto destroyer = self.destroy_on_scope_exit();
        
        return std::move(self).core_task_awaiter_result_base::core_task_variant_result::await_resume();
    }

    using core_task_awaiter_result_base::single_owner_promise_handle::single_owner_promise_handle;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result
> class core_reusable_task_promise_base
    :
    public core_task_variant_result<Result>
{
public:
    static constexpr bool is_reusable = true;
};

PHANTOM_COROUTINES_MODULE_EXPORT
template<
    typename Result
> class core_non_reusable_task_promise_base
{
public:
    static constexpr bool is_reusable = false;

    core_task_variant_result<Result>* m_result;

    core_task_variant_result<Result>& result()
    {
        return *m_result;
    }

    void unhandled_exception()
    {
        result().unhandled_exception();
    }

    void return_exception(
        std::exception_ptr exception)
    {
        result().return_exception(
            std::move(exception));
    }

    void return_variant_result(
        auto&& value
    )
    {
        result().return_variant_result(
            std::forward<decltype(value)>(value));
    }
};

template<
    typename Result,
    is_continuation Continuation,
    template<typename Result> typename PromiseBase
> class core_task_promise
    :
    public extensible_promise,
    public variant_return_result<Result>,
    public PromiseBase<Result>
{
    template<
        typename Promise
    > friend class core_task;

    template<
        typename Promise
    > friend class core_task_awaiter;

private:

    Continuation m_continuation;

protected:
    Continuation& continuation()
    {
        return m_continuation;
    }

public:
    typedef Result result_type;
    typedef Continuation continuation_type;

    auto initial_suspend(
    ) noexcept
    {
        return suspend_always{};
    }

    auto final_suspend(
    ) noexcept
    {
        return final_suspend_transfer{ continuation() };
    }

    auto get_return_object(
        this auto& self
    ) noexcept
    {
        return core_task
        {
            self
        };
    }

    using PromiseBase<Result>::return_exception;
    using PromiseBase<Result>::return_variant_result;
    using PromiseBase<Result>::unhandled_exception;
};

template<
    typename Promise
> class core_task_awaiter
    :
    public core_task_awaiter_result_base<Promise>
{
protected:

    template<
        typename Result,
        is_continuation Continuation
    > friend class basic_reusable_task_promise;

public:
    using core_task_awaiter::core_task_awaiter_result_base::core_task_awaiter_result_base;

    bool await_ready(
    ) const noexcept
    {
        return !this->handle() || this->handle().done();
    }

    auto await_suspend(
        this auto& self,
        auto awaiter
    ) noexcept
    {
        self.set_promise_variant_result_pointer();
        self.promise().continuation() = awaiter;
        return self.handle();
    }

    decltype(auto) get_result_value(
        std::invocable auto&& expression
    )
    {
        return std::forward<decltype(expression)>(expression)();
    }
};

template<
    typename Promise
>
class [[nodiscard]] core_task
    :
    public single_owner_promise_handle<Promise>
{
public:
    using single_owner_promise_handle<Promise>::single_owner_promise_handle;
    using promise_type = Promise;
    static constexpr bool is_reusable = promise_type::is_reusable;

    auto when_ready(
        this auto& self
    ) noexcept requires is_reusable
    {
        struct [[nodiscard]] awaiter : core_task_awaiter<Promise>
        {
            using awaiter::core_task_awaiter::core_task_awaiter;

            void await_resume()
            {
            }
        };

        return awaiter
        {
            self.handle()
        };
    }

    template<
        typename Self
    > auto operator co_await(
        this Self&& self
        ) noexcept
        requires
    !std::is_lvalue_reference_v<Self>
        || is_reusable
    {
        struct [[nodiscard]] awaiter : core_task_awaiter<Promise>
        {
            using awaiter::core_task_awaiter::core_task_awaiter;

            decltype(auto) await_resume()
            {
                return std::forward_like<Self>(*this).core_task_awaiter::await_resume();
            }
        };

        return awaiter
        {
            std::forward_like<Self>(self.handle())
        };
    }
};

template<typename Promise>
core_task(coroutine_handle<Promise>) -> core_task<Promise>;

}
#endif
