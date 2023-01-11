# [Phantom.Coroutines](../README.md)

## ```async_generator.h```

```async_generator``` allows writing enumerators that may require asynchronous operation. 
The pattern for using an async_generator is:

```c++
task<> something_async();

std::string get_string();

async_generator<std::string> enumerate_strings(bool returnLast)
{
    // Yields a reference to a temporary value
    co_yield "hello world";
    
    std::string value = get_string();
    // Yields a reference to a -copy- of the l-value value
    co_yield value;

    // Waits for another task to complete before yielding more items
    co_await something_async();
    
    // Yields a reference to the r-value
    co_yield get_string();

    if(!return_last)
    {
        co_return;
    }

    // Yields a reference to a temporary value
    co_yield "last";
}

task<> do_something_with_enumeration()
{
    // Note there is no "co_await" on enumerate_strings()
    auto enumeration = enumerate_strings();

    for(
        // begin() needs to be co_await'ed, and returns an iterator
        auto iterator = co_await enumeration.begin();
        
        // end() should not be co_await'ed
        iterator != enumeration.end();
        
        // ++iterator needs to be co_await'ed
        co_await ++iterator)
    {
        // The value of the iterator is accessed via *iterator,
        // which returns a reference to the co_yield'ed value.
        std::cout << *iterator;
    }
}
```

### ```async_generator<Result, Policies...>```

The ```async_generator``` type accepts a ```Result``` type argument to return from the
iterator. This type _may_ be a reference type. The semantics of Result being
an various reference types and yield values of various reference types are as follows:

* ```Result``` is ```T```, ```co_yield T&```:

  ```*iterator``` is a ```T&``` to a copy of the value referenced in the ```co_yield``` statement

* ```Result``` is ```T```, ```co_yield T``` or ```co_yield T&&```:

  ```*iterator``` is a ```T&``` to the original value referenced in the ```co_yield``` statement

* ```Result``` is ```T&```, ```co_yield T&```:

  ```*iterator``` is a ```T&``` to the original value referenced in the ```co_yield``` statement

* ```Result``` is ```T&```, ```co_yield T``` or ```co_yield T&&```:

  ```*iterator``` is a ```T&``` to the value referenced in the ```co_yield``` statement

The implication here is that the following code is probably not the most performant:

```c++
async_generator<std::string> get_strings()
{
    std::string result = "hello world";
    // This will _copy_ result, because the co_yield
    // is referencing an l-value
    co_yield result;
}
```

Instead, say:


```c++
async_generator<std::string> get_strings()
{
    std::string result = "hello world";
    // *iterator returns a reference to the original result, without
    // actually doing a move-construct operation.
    co_yield std::move(result);
}
```

or:


```c++
async_generator<std::string> get_strings()
{
    // *iterator returns an r-value reference to the temporary variable, without
    // actually doing a move-construct operation.
    co_yield "hello world";
}
```

### ```base_promise_type<T>``` policy

```async_generator<Result, Policies...>``` and ```async_generator_promise<Result, Policies...>``` accept 
a ```base_promise_type<Promise>``` policy to specify
the backing promise type, which defaults to [```task_promise<Result>```](task.md#task_promise). 
```async_generator``` can use any backing promise which supports these facilities:

1. The ```get_return_object()``` method call of ```Promise``` is awaitable (which
   is true of all ordinary promise objects).
2. The value of [```get_awaiter```](type_traits.md#get_awaiter)```(get_return_object())```
   is an awaiter.
3. The awaiter's ```await_ready()``` and ```await_suspend()``` methods can
   be called multiple times, with each ```await_suspend()``` replacing
   the current continuation of the underlying ```Promise```. 
4. The awaiter's ```await_resume()``` method can be called zero or one times.
   It will be called when the enumeration is complete.
5. The awaiter type possesses a method matching the signature:

   ```c++
    decltype(auto) get_result_value(
        std::invocable iterator
    );
   ```

   This method is used to translate an ```iterator_type``` into the
   correct type to return from ```co_await iterator_type::operator++```
   and ```co_await async_generator<>::begin()``` when the enumeration is returning
   a valid iterator.

6. The Awaiter type possesses a method matching the signature:

   ```c++
    decltype(auto) await_resume_value(
        std::invocable iterator
    );
   ```

   This method is used to translate an ```iterator_type``` into the
   correct type for callers to```co_await iterator_type::operator++```
   and ```co_await async_generator<>::begin()``` when the enumeration has completed, either
   by an explicit ```co_return``` statement, falling off the end of the
   coroutine body, or by an exception. In the exception case, the ```resume_result```
   method should throw the exception or return the expected error type.

Phantom.Coroutines provides these core promise types that meet these requirements:

* [```task_promise```](task.md)
* [```early_termination_promise```](early_termination_task.md#early_termination_promise)

These attributes are embodied by the concept ```is_async_generator_base_promise<T>```.
