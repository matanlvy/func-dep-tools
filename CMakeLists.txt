cmake_minimum_required(VERSION 3.14)

project(func_dep_tools)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# ---- GoogleTest ----
include(FetchContent)

FetchContent_Declare(
  googletest
  URL https://github.com/google/googletest/archive/refs/heads/main.zip
)

set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# ---- Main program ----
add_executable(func_dep_tools main.cpp)

# ---- Enable testing ----
enable_testing()

# ---- Tests ----
add_subdirectory(tests)