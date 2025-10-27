method helper(x: Int): Int
    requires x >= 0
    ensures result >= 0
{
    return x + 1
}

method main()
{
    var res: Int;
    res := helper(5);
    assert res > 0
}