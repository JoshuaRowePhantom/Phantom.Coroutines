# [Phantom.Coroutines](../README.md)

## Conventions

The Phantom.Coroutines implementation follows these conventions.

### return_, get_ names

```return_value``` is reserved by the C++ standard to indicate the promise can accept a return value. 

```return_void``` is reserved by the C++ standard to indicate the promise can return a void value.

```value``` in the library refers to a value provided by the C++ runtime or a user. ```result`` refers
to a value being _returned_ to the caller or user.

```get_``` means to obtain, with as little interpretation as possible, the specified value name.

```return_``` means to obtain for the use of a caller the specified value name in a context where
the value will be used to resume a caller.
