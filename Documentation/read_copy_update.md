# [Phantom.Coroutines](../README.md)

## ```read_copy_update.h```

```read_copy_update.h``` provides a read-copy-update section in the class ```read_copy_update<T>```.
A read-copy-update section has very high read performance. 

See [https://en.wikipedia.org/wiki/Read-copy-update].

## ```read_copy_update<typename T>```

```read_copy_update<typename T>``` implements a read-copy-update section
holding at least one instance of T. 