# Building Phantom.Coroutines

Phantom.Coroutines uses [CMake](https://cmake.org/) (3.30+) with [vcpkg](https://vcpkg.io/) for dependency management and [Ninja](https://ninja-build.org/) as the build generator.

## Prerequisites

- CMake 3.30 or later
- Ninja
- vcpkg (set `VCPKG_ROOT` environment variable to your vcpkg installation)
- A supported compiler:
  - **Windows:** MSVC (Visual Studio 2026 or later) or Clang
  - **Linux:** Clang 21

## Configure

Use a CMake preset to configure. For development, prefer a **debug** preset:

```
cmake --preset msvc-windows-x64-debug
```

Available presets (defined in `CMakePresets.json`):

| Preset | Platform | Compiler | Config |
|---|---|---|---|
| `msvc-windows-x64-debug` | Windows | MSVC | Debug |
| `msvc-windows-x64-release` | Windows | MSVC | RelWithDebInfo |
| `clang-windows-x64-debug` | Windows | Clang | Debug |
| `clang-windows-x64-release` | Windows | Clang | RelWithDebInfo |
| `clang-linux-x64-debug` | Linux | Clang 21 | Debug |
| `clang-linux-x64-release` | Linux | Clang 21 | RelWithDebInfo |

> **Note:** The release configuration is `RelWithDebInfo` (not `Release`). It enables link-time code generation (`/GL`/`/LTCG`) on MSVC.

> **Note:** Debug builds on MSVC enable AddressSanitizer (`/fsanitize=address`).

### Local overrides

`CMakeUserPresets.json` provides `*-local` variants of the Clang presets that hard-code local compiler paths. Copy and adapt as needed for your machine.

## Build

```
cmake --build --preset msvc-windows-x64-debug
```

Replace the preset name to match your configured preset.

## Run Tests

```
ctest --preset msvc-windows-x64-debug-unit
```

Test presets mirror the configure presets. Tests take roughly 5 seconds to run.

## Visual Studio

Open the repository folder in Visual Studio. It will detect `CMakePresets.json` automatically. Select a preset from the configuration drop-down and build/run tests from the IDE.

## Building with VS2026 PowerShell

From a **Visual Studio 2026 Developer PowerShell** session, cmake, ninja, cl, and the Windows SDK are all on `PATH` and the MSVC environment variables (`INCLUDE`, `LIB`) are set correctly. Use the VS Developer PowerShell shortcut, or load it yourself:

```powershell
Import-Module "C:\Program Files\Microsoft Visual Studio\18\Enterprise\Common7\Tools\Microsoft.VisualStudio.DevShell.dll"
Enter-VsDevShell -VsInstallPath "C:\Program Files\Microsoft Visual Studio\18\Enterprise" -Arch amd64 -SkipAutomaticLocation
```

Then configure (only needed once, or after clearing the cache):

```powershell
cmake --preset msvc-windows-x64-debug
```

Build the C++ modules test target (iterative development):

```powershell
cmake --build --preset msvc-windows-x64-debug --target Phantom.Coroutines.Modules.Test
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Modules.Test.exe
```

Full build and test suite (run when done with a task):

```powershell
cmake --build --preset msvc-windows-x64-debug
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.Modules.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.Test\Phantom.Coroutines.SingleModule.Test.exe
.\out\build\msvc-windows-x64-debug\Phantom.Coroutines.cppcoro.Test\Phantom.Coroutines.cppcoro.Test.exe
```

> **Note:** Use the test executables directly rather than `ctest`, as ctest spawns each test case as a separate process which is slow with AddressSanitizer enabled.

> **Note:** If configure fails with `Could NOT find GTest`, delete `out\build\msvc-windows-x64-debug\CMakeCache.txt` and re-run configure. This can happen when the build directory was previously configured with a different toolchain.

## C++ Modules

The `Phantom.Coroutines.Modules` target builds C++ module support. Module linking is disabled for Clang builds (`DISABLE_LINK_MODULES=ON`) and can be disabled entirely with `-DDISABLE_COMPILE_MODULES=ON`.
