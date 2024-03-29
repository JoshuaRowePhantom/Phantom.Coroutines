#include "contextual_promise.h"
#include "thread_local_context.h"

namespace Phantom::Coroutines
{
namespace detail
{

template<
    is_thread_local_context ThreadLocalContext,
    typename BasePromise
> class thread_local_contextual_promise
    :
    public derived_promise
    <
        contextual_promise
        <
            BasePromise
        >
    >
{
    using base_promise = thread_local_contextual_promise::derived_promise;
    using thread_local_context_scope = thread_local_context_scope<ThreadLocalContext>;

public:
    using value_type = typename ThreadLocalContext::value_type;

private:
    std::optional<thread_local_context_scope> m_scope;
    std::optional<value_type> m_value;

public:
    template<
        typename... Args
    > thread_local_contextual_promise(
        Args&&... args
    ) :
        thread_local_contextual_promise::derived_promise{ std::forward<Args>(args)... },
        m_value
    {
        ThreadLocalContext::current()
    }
    {}

    using base_promise::base_promise;

    void enter()
    {
        m_scope.emplace(std::move(*m_value));
        m_value.reset();
    }

    void leave()
    {
        m_value.emplace(std::move(ThreadLocalContext::current()));
        m_scope.reset();
    }
};

}
using detail::thread_local_contextual_promise;
}