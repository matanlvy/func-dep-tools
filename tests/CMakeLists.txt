add_executable(
    func_dep_tools_tests
    func_dep_tools_tests.cpp
)

target_link_libraries(
    func_dep_tools_tests
    GTest::gtest_main
)

include(GoogleTest)

gtest_discover_tests(func_dep_tools_tests)