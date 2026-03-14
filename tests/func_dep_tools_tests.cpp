#include <gtest/gtest.h>

TEST(BasicTest, AdditionWorks)
{
    EXPECT_EQ(2 + 2, 4);
}

TEST(BasicTest, BooleanCheck)
{
    EXPECT_TRUE(1 < 2);
}