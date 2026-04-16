# Phantom.Coroutines Tracing

The tracing system allows coroutine lifecycle events to be observed by attaching a *trace sink* to a
`traced_promise`. The traced promise emits strongly-typed events before and after every coroutine
lifecycle operation (initial/final suspend, `co_await`, `co_yield`, `co_return`, etc.) and delivers
them to the trace sink.

All tracing types live in `Phantom::Coroutines::tracing`.

---

## Trace Sinks

A *trace sink* is any callable object. The `is_trace_sink` concept accepts every type:

```cpp
template<typename TraceSink>
concept is_trace_sink = true;
```

The trace sink is called with two distinct kinds of arguments:

| Argument kind | Purpose |
|---|---|
| `const events::event<...>&` | A lifecycle event has occurred — record or act on it. |
| `const events::should_trace_return_value<Event>&` | A query asking whether to capture the return value for the next result event. |
| `const events::should_capture_promise_creation_arguments<Event>&` | A query asking whether to capture promise creation arguments. |

The two query types are described in detail below.

---

## Events

Every event is an instance of `events::event<EventType, EventData, Accessors...>`. The three
members of interest are:

| Member | Type | Description |
|---|---|---|
| `SourceLocation` | `std::source_location` | Where the `co_await`/`co_yield`/etc. appears in source. |
| `EventType` | `events::event_type<Label>` | Identifies the kind of event (e.g. `await_ready_result`). |
| `EventData` | `events::event_data<...>` | Contextual data for the event (see below). |

The convenience function `events::basic_event(sourceLocation, label, eventData)` builds a
fully-typed event value.

### Event labels

Events are emitted in *begin / result / exception* triples for each operation:

| Operation | Begin | Result | Exception |
|---|---|---|---|
| `initial_suspend` | `await_ready_begin` | `await_ready_result` | `await_ready_exception` |
| `await_suspend` | `await_suspend_begin` | `await_suspend_result` | `await_suspend_exception` |
| `await_resume` | `await_resume_begin` | `await_resume_result` | `await_resume_exception` |
| `await_transform` | `await_transform_begin` | `await_transform_result` | `await_transform_exception` |
| `unhandled_exception` | `unhandled_exception_begin` | `unhandled_exception_result` | `unhandled_exception_exception` |
| `get_return_object` | `get_return_object_begin` | `get_return_object_result` | `get_return_object_exception` |
| `yield_value` | `yield_value_begin` | `yield_value_result` | `yield_value_exception` |
| `return_value` | `return_value_begin` | `return_value_result` | `return_value_exception` |
| `return_void` | `return_void_begin` | `return_void_result` | `return_void_exception` |

Additionally, `create_promise` and `destroy_promise` are emitted from the `traced_promise`
constructor and destructor respectively.

Each label type also inherits one or more tag structs (`event_is_begin`, `event_is_result`,
`event_is_await_ready`, etc.) so filters can match broad categories without naming every label.

### `event_data`

`events::event_data<...>` is a template whose type parameters reflect which fields are populated.
Fields that are absent use `empty_value` (or `empty_arguments_value` / `no_awaiter_type` for their
respective categories). The `with()` method merges two `event_data` values, taking non-empty fields
from the argument over empty fields from the receiver.

| Field | Type when populated | Description |
|---|---|---|
| `Promise` | `T*` | Pointer to the underlying (untraced) promise. |
| `TracedPromise` | `T*` | Pointer to the `traced_promise`. |
| `PromiseCreationArguments` | `events::arguments<Args...>` | Arguments forwarded to the promise constructor (only when opted-in via `should_capture_promise_creation_arguments`). |
| `Awaiter` | `T*` | Pointer to the wrapped awaiter. |
| `TracedAwaiter` | `T*` | Pointer to the `traced_awaiter`. |
| `AwaiterType` | One of the `*_awaiter_type` tag structs | Whether this awaiter is for initial suspend, final suspend, `co_yield`, or `co_await`. |
| `MethodArguments` | `events::arguments<Args...>` | Arguments passed to the method (e.g. the handle for `await_suspend`, the value for `yield_value`). |
| `MethodResult` | `events::value<T>` | Return value of the method — only present when opted-in via `should_trace_return_value`. |
| `MethodException` | `events::value<std::exception_ptr>` | Exception caught by the method. |
| `UnhandledException` | `events::value<std::exception_ptr>` | Exception from `unhandled_exception`. |
| `YieldValue` | `events::value<T>` | Value passed to `co_yield`. |
| `ReturnValue` | `events::value<T>` | Value passed to `co_return`. |

---

## Query protocol

Two query types exist so the trace sink can control expensive optional features at compile time
(and optionally at runtime).

### `should_trace_return_value<Event>`

By default, result events (e.g. `await_ready_result`) do **not** include the method's return value
in `EventData.MethodResult`. Capturing the return value requires the value to be move- or
copy-constructible and the trace sink to explicitly opt in.

Before calling the wrapped method, `call_traced_method` checks the trace sink:

1. **Sink not invocable** with `should_trace_return_value<Event>`, or **invocable but returns `void`**
   → return value is **not** traced; `MethodResult` is `empty_value`.

2. **Invocable and returns `std::true_type`**
   → return value is **always** traced (compile-time decision, zero overhead).

3. **Invocable and returns `std::false_type`**
   → return value is **never** traced (compile-time decision).

4. **Invocable and returns `bool`**
   → the sink is queried at runtime; the return value is traced only when the query returns `true`.

The `Event` template parameter of `should_trace_return_value<Event>` is the full `event_data` type
that the result event *would* carry if the return value were traced (including all contextual fields
such as `AwaiterType`). This lets the sink inspect which operation is being traced before deciding.

#### Example: opting in unconditionally

The helper `filters::trace_return_value(traceSink)` wraps any trace sink and adds a handler that
returns `std::true_type` for every `should_trace_return_value` query:

```cpp
auto sink = filters::trace_return_value(my_trace_sink);
// sink now receives result events with MethodResult populated.
```

#### Example: implementing the query manually

```cpp
struct my_trace_sink
{
    // Record lifecycle events.
    void operator()(const auto& event) { /* ... */ }

    // Opt in to return-value tracing for await_ready only.
    std::true_type operator()(
        const events::should_trace_return_value<auto>& query) const noexcept
        requires events::is_event_type<
            typename decltype(query)::event_type,
            events::await_ready_result>
    {
        return {};
    }
};
```

> **Note:** filters such as `awaiter_type_fn` do *not* satisfy `should_trace_return_value` queries,
> because `should_trace_return_value<Event>` has only a `using event_type = Event` member — it does
> not expose `EventData`. A trace sink that only wraps a filter (and whose `operator()` returns
> `void`) will **never** trace return values. Use `trace_return_value()` or add an explicit query
> handler as shown above.

### `should_capture_promise_creation_arguments<PromiseCreationEvent>`

The same three-way protocol (`void` / `std::true_type` / `std::false_type` / `bool`) applies to
`should_capture_promise_creation_arguments`. When opted-in, `PromiseCreationArguments` in the
`create_promise` event data is populated with all arguments forwarded to the promise constructor.

---

## Filters

Filters live in `Phantom::Coroutines::tracing::filters`. They are callable objects derived from
`filters::filter` that return `std::true_type`, `std::false_type`, or `bool` depending on whether a
given event matches. The `filter` base class provides a catch-all `operator()` that returns
`std::false_type` for unrecognised event types.

Filters compose with `&&`, `||`, and `!`. The composed result is again a `filter` that propagates
compile-time `true_type`/`false_type` when possible.

### Built-in filters

| Filter | Matches |
|---|---|
| `filters::any_event` | Every event — always returns `std::true_type`. |
| `filters::event_type<Label...>` | Events whose label type is one of `Label...`. |
| `filters::awaiter_type<AwaiterType>` | Events whose `EventData.AwaiterType` is exactly `AwaiterType`. |

### `constant_filtered_trace_sink` / `runtime_filtered_trace_sink`

These helpers wrap a filter and a trace sink into a new trace sink:

```cpp
// Compile-time filtering: the sink call is entirely elided when filter(event) == false_type.
auto sink = filters::constant_filtered_trace_sink(
    filters::awaiter_type<events::initial_suspend_awaiter_type>,
    my_trace_sink);

// Runtime filtering.
auto sink = filters::runtime_filtered_trace_sink(my_filter, my_trace_sink);
```

> **Note:** Queries (`should_trace_return_value`, `should_capture_promise_creation_arguments`)
> bypass the filter entirely and are forwarded directly to the inner sink. The filter determines
> which *events* to trace, not whether to answer interrogations about tracing behaviour.

---

## `traced_promise` and `traced_awaiter`

`traced_promise<TraceSink, BasePromise>` wraps any `extensible_promise`-based promise type and
intercepts every coroutine lifecycle method. It stores the trace sink and forwards it to each
`traced_awaiter` it creates.

`traced_awaiter<TraceSink, Awaitable, AwaiterType, BaseEventData>` wraps an awaitable and
intercepts `await_ready`, `await_suspend`, and `await_resume`.

Both use `call_traced_method` internally, which handles begin/result/exception event emission and
the `should_trace_return_value` query protocol.

### `suppress_trace`

Wrap an awaitable in `suppress_trace{awaitable}` to bypass `await_transform` tracing for that
particular `co_await`:

```cpp
co_await suppress_trace{ m_event.Wait() };
```

### Custom `trace` events

Any `co_await` of a type derived from `tracing::trace` is intercepted and forwarded directly to the
trace sink without suspending the coroutine:

```cpp
struct my_event : tracing::trace { /* fields */ };

// Inside a coroutine whose promise is a traced_promise:
co_await my_event{ /* data */ };
```

---

## `composed_function`

`composed_function<F1, F2, ...>` (from `functional.h`) inherits `operator()` from each function in
the pack via `using`. This is the mechanism used by `trace_return_value()` to bolt a
`should_trace_return_value` handler onto an existing trace sink without wrapping it in an outer
lambda that would hide the query handler from the template machinery.
