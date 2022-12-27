# [Phantom.Coroutines](../README.md)

## ```async_scope.h```

The ```async_scope``` class allows starting a series of background tasks
and waiting for all of them to complete. Any awaitable / awaiter object
can be passed to ```async_scope::spawn```. To wait for all the pending objects,
call ```async_scope::join```. It is an error to ```spawn``` more tasks after
calling ``join```; the result of calling ``spawn``` after calling ```join`` is
controlled by the [```use_after_join_policy```](policies.md#use_after_join_policy).

Most awaitable objects in ```Phantom.Coroutines``` start upon a ```co_await``` operation,
and run lazily. ```async_scope``` provides a mechanism to start operations
eagerly, as the operation is ```co_await```'ed before ```spawn``` returns.

Any return value from these tasks is ignored. Any unhandled exception will be uncaught
and dealt with by the default C++ semantics.

```
task<> Task1();
task<> Task2();

task<> ControllingTask()
{
    async_scope scope;
    scope.spawn(Task1());
    scope.spawn(Task2());
    co_await scope.Join();
    // This is illegal:
    // scope.spawn(Task3());
}
```
