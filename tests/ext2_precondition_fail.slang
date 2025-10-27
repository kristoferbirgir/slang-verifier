method helper(x: Int): Int
    requires x >= 10  // Requires x >= 10
    ensures result >= 0
{
    return x + 1
}

method main()
{
    var res: Int;
    res := helper(5);  // Basic implementation doesn't check preconditions yet
    assert res > 0
}