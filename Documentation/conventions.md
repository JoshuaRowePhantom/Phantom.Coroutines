# [Phantom.Coroutines](../README.md)

## Conventions

The Phantom.Coroutines implementation follows these conventions.

### Use of explicit object argument deduction

Most methods in the library use the C++23 construct ```this auto& self``` as the explicit argument.
This eliminates the need to use the [curiously recurring template pattern](https://www.bing.com/search?q=curiously+recurring+template+pattern)
and virtual functions to implement extensibility. Instead, objects generally are expected to accept knowledge
of the exact type of the object via this parameter.

### return_, get_, resume_ names

```return_``` accepts a value _into_ a promise object for the purpose of later resuming
the awaiter which will obtain that value. Notably, ```return_value``` and ```return_void```
in the C++ standard follow this pattern.

```value``` in the library refers to a value provided by the C++ runtime or a user. ```result`` refers
to a value being _returned_ to the caller or user.

```get_``` means to obtain, with as little interpretation as possible, the specified value name.

```resume_``` means to obtain for the use of a caller the specified value name in a context where
the value will be used to resume a caller.

### basic_ names

A ```basic_``` name represents the raw, low-level type implementing a concept. These names
have more implementation details associated with them about how they work, and users using
these names should expect significant changes from one version of Phantom.Coroutines to the next.

For example, [```task```](task.md) is an alias to ```basic_task```. ```task``` accepts user-friendly policy-driven
type arguments, whereas ```basic_task``` accepts the ```promise_type``` to use. Similarly,
```task_promise``` also accepts user-friendly policy-driven type arguments, whereas ```basic_task_promise```
accepts specific type arguments for each supported policy.

