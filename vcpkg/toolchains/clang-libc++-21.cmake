set(CMAKE_C_COMPILER "clang-21")
set(CMAKE_CXX_COMPILER "clang++-21")
add_compile_options(-stdlib=libc++)
add_link_options(-stdlib=libc++)
