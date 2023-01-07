# [Phantom.Coroutines](../README.md)

## Conventions

The Phantom.Coroutines implementation follows these conventions.

### return_, get_ names

```return_``` accepts a value _into_ a promise object for the purpose of later resuming
the awaiter which will obtain that value. Notably, ```return_value``` and ```return_void```
in the C++ standard follow this pattern.

```value``` in the library refers to a value provided by the C++ runtime or a user. ```result`` refers
to a value being _returned_ to the caller or user.

```get_``` means to obtain, with as little interpretation as possible, the specified value name.

```resume_``` means to obtain for the use of a caller the specified value name in a context where
the value will be used to resume a caller.
