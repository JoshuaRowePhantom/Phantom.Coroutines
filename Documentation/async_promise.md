# [Phantom.Coroutines](../README.md)

## ```async_promise.h```

```async_promise<Value, Event>``` provides a standard way to expose the
future ability to acquire a value, wrapping the ordinary
construct of a ```Value``` that is available after some ```Event```
has been signalled.

The default ```Event``` type is [```async_manual_reset_event<>```](async_manual_reset_event.md). The ```Value``` type is returned by reference when ```co_await```'ing the ```async_promise<>```. The value can be provided either at construction time
or by calling the ```emplace``` method.

```c++
async_promise<std::wstring> myDelayedString;

task<> UseDelayedString()
{
    std::cout << co_await myDelayedString;
}

task<> AcquireTheString()
{
    // ... do some things here
    myDelayedString.emplace(L"Hello world");
    // ... do some more things here
    co_return;
}

task<> HelloWorld()
{
    async_scope<> scope;
    scope.spawn(UseDelayedString());
    scope.spawn(AcquireTheString());
    co_await scope.join();
}
```
