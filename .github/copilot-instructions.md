# Copilot Instructions

## Build Configuration

**Always use debug builds when developing and testing.** Use the appropriate debug preset for your platform:

- **MSVC on Windows:** `msvc-windows-x64-debug`
- **Clang on Windows:** `clang-windows-x64-debug` (or `clang-windows-x64-debug-local` if using `CMakeUserPresets.json`)
- **Clang on Linux:** `clang-linux-x64-debug` (or `clang-linux-x64-debug-local` if using `CMakeUserPresets.json`)

Debug builds enable AddressSanitizer (`/fsanitize=address`) on MSVC, which helps catch memory errors during development.

**All build and test commands must be run from a Visual Studio 2026 Developer PowerShell session.** Load it with:

```powershell
Import-Module "C:\Program Files\Microsoft Visual Studio\18\Enterprise\Common7\Tools\Microsoft.VisualStudio.DevShell.dll"
Enter-VsDevShell -VsInstallPath "C:\Program Files\Microsoft Visual Studio\18\Enterprise" -Arch amd64 -SkipAutomaticLocation
```

See [BUILDING.md](../BUILDING.md) for full build instructions.

## Project Overview

Phantom.Coroutines is a C++23 coroutine library with two implementation options:

- **Header-only:** include headers from `Phantom.Coroutines/include/`
- **C++ Modules:** build and link against the `Phantom.Coroutines.Modules` CMake target

Tests are in `Phantom.Coroutines.Test/` and cppcoro-compatibility tests in `Phantom.Coroutines.cppcoro.Test/`.

## Testing

### During development (iterative)

Build and run only the C++ modules implementation and its tests. This is faster and catches most issues:

```
cmake --build --preset msvc-windows-x64-debug --target Phantom.Coroutines.Modules.Test
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Modules.Test.exe
```

### When a task is complete (full suite)

Build everything and run all three test executables:

```
cmake --build --preset msvc-windows-x64-debug
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Modules.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.SingleModule.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.cppcoro.Test\Phantom.Coroutines.cppcoro.Test.exe
```

All PRs must include unit tests. Follow the existing naming style: descriptive test names with single-purpose assertions.
