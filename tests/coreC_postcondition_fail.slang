// Test case 2: Postcondition failure
method test_postcondition_fail(x: Int): Int
    requires x >= 0
    // @CheckError
    ensures result > x + 10
{
    return x + 5
}